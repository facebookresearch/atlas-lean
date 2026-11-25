# Forward filtering with backward sampling draws the exact posterior path

Let $h$ be the canonical [hidden Markov model](hmm.md) on a finite state set $S$, with nonnegative real initial, transition and emission weights $\pi$, $a$, $e$. The weights need not be normalized. Fix $T\in\mathbb N$ and observations $x_0,\dots,x_T$, with the observation at time zero emitted from the initial state. Let $\alpha_t$ be the [forward variables](forward.md), so $\alpha_0(s)=\pi(s)e(s,x_0)$ and $\alpha_{t+1}(j)=e(j,x_{t+1})\sum_s\alpha_t(s)a(s,j)$. Suppose $L=\sum_s\alpha_T(s)>0$.

Write $w(z)$ for the canonical [joint path weight](path-prob.md). By the [forward likelihood identity](likelihood-eq-sum-forward.md), $L=\sum_{z\in S^{T+1}}w(z)$. Here the posterior path law means the normalized finite weight $w(z)/L$; it agrees with conditional HMM probability when the weights specify a probabilistic model. Use exact conditional categorical draws, with fresh independent randomization at each step; finite-precision implementations are not covered.

## Backward sampler and support

Draw $Z_T$ with mass $\alpha_T(j)/L$. For $t=T-1,\dots,0$, define $D_t(j)=\sum_s\alpha_t(s)a(s,j)$ and, conditional on the already drawn suffix with $Z_{t+1}=j$, draw $Z_t$ from

$$ B_t(j,s)=\begin{cases}\alpha_t(s)a(s,j)/D_t(j),&D_t(j)>0,\\q_*(s),&D_t(j)=0,\end{cases} $$

where $q_*$ is any fixed probability law on $S$ (for example, a point mass; $L>0$ implies $S$ is nonempty). Then every row of $B_t$ is a probability law, and

$$\mathbb P(Z_0=z_0,\dots,Z_T=z_T)=\frac{w(z)}{L}\qquad\text{for every }z\in S^{T+1}.$$

The zero-row completion has no effect on the output law. Indeed $\alpha_T(Z_T)>0$ almost surely. If $\alpha_{t+1}(j)>0$, its factorization $\alpha_{t+1}(j)=e(j,x_{t+1})D_t(j)$ and nonnegativity imply both $e(j,x_{t+1})>0$ and $D_t(j)>0$. Any predecessor drawn with positive mass then has $\alpha_t(s)>0$. Backward induction therefore never reaches a zero-normalizer row. This proves positivity before using the identity $D_t(j)=\alpha_{t+1}(j)/e(j,x_{t+1})$; that quotient is not asserted at an emission-zero state.

For a path of positive weight, all its prefix forward weights are positive by the [path-sum interpretation of the forward variables](forward-eq.md). Multiplying its final draw and backward draws now permits cancellation and gives

$$\frac{\alpha_T(z_T)}{L}\prod_{t=0}^{T-1}\frac{\alpha_t(z_t)a(z_t,z_{t+1})e(z_{t+1},x_{t+1})}{\alpha_{t+1}(z_{t+1})}=\frac{\pi(z_0)e(z_0,x_0)\prod_{t=0}^{T-1}a(z_t,z_{t+1})e(z_{t+1},x_{t+1})}{L}.$$

Conversely a path drawn with positive probability has positive initial and emission weights and positive transition weights along it, by the support argument. It therefore has $w(z)>0$. All zero-weight paths consequently have sampler probability zero, which proves the formula without canceling a zero factor.

For $T=0$ there is one observed time and no backward draw, so the result is just normalization of $\pi(s)e(s,x_0)$. No posterior claim is made when $L=0$. This is joint-path sampling, not independent draws from the smoothed marginals or coordinatewise posterior decoding: with two states, equal initial weights, identity transitions and unit emissions, the two constant length-two paths have mass $1/2$ each and the changing paths have mass zero.

## Block Gibbs consequence, allowing zeros

Let $\Pi$ be a probability mass function on finite sets $\mathcal Z\times\mathcal Y$, where $\mathcal Z$ is the path block, and put $p_Y(y)=\sum_z\Pi(z,y)$. For every $y$ with $p_Y(y)>0$, suppose a positive-likelihood HMM posterior as above is exactly $F_y(z)=\Pi(z,y)/p_Y(y)$. For a zero-mass fiber choose any probability law $F_y$. The update that keeps $y$ fixed and draws a new path by FFBS on positive fibers, using the arbitrary completion on zero fibers, has kernel $Q((z,y),(z',y'))=\mathbf1[y=y']F_y(z')$ and preserves $\Pi$, since

$$\sum_z\Pi(z,y)F_y(z')=p_Y(y)F_y(z')=\Pi(z',y).$$

When $p_Y(y)=0$, both sides are zero because every $\Pi(z,y)$ is zero. On a positive fiber the detailed-balance product is $\Pi(z,y)\Pi(z',y)/p_Y(y)$, which is symmetric. Thus no full-support assumption on the target is needed. This finite-sum argument supplies the block and zero-mass cases directly; a full-support coordinate Gibbs theorem alone does not cover them. Stationarity does not by itself establish convergence or mixing from an arbitrary initial state.

## Position-dependent states and the threading application

The same finite-weight result handles finite state sets $S_t$ and position-dependent transition/emission weights without introducing another HMM representation. Use the canonical HMM on the tagged disjoint union of the $S_t$: initial mass is supported on layer zero, transitions go only from $(t,s)$ to $(t+1,j)$ with the desired weight, and observation $x_t$ is tagged with $t$, making all emissions from other layers zero. Paths of nonzero weight correspond exactly to the original position-dependent paths; the forward recurrence and backward sampler restrict to the corresponding layers.

Rasmussen and colleagues use stochastic traceback to sample a coalescence threading after marginalizing new recombination variables. Applying this theorem to a discretized-SMC posterior remains conditional on proving that its actual conditional weights and support are exactly this HMM factorization. Moreover, a full threading includes the new recombination variables: after sampling the coalescence path $z$, these must also be drawn from their correct conditional law given $z$ and the retained history $y$. The chain rule then recovers the joint threading conditional. Drawing only $z$ and keeping an old, correlated recombination state need not preserve that joint target.

## Expansion

The discretized-SMC application requires its own model and state/weight correspondence, including the position-dependent state support, the integrated-out recombination weights, and the conditional reconstruction of recombinations. For a concrete two-leaf discretized-SMC model, prove that the full threading update leaves its posterior invariant; generic HMM examples do not discharge this application. This page does not certify an ARGweaver implementation or the continuous ARG posterior. The source also distinguishes single-sequence Gibbs updates from state-dependent subtree proposals, which require a Hastings correction, and from sequential initialization, which is not itself a posterior draw.

## Depends on

- [Hidden Markov model](hmm.md)
- [Forward variables of a hidden Markov model](forward.md)
- [Joint weight of a state path and the observations](path-prob.md)

## Proof depends on

- [The forward variables are path sums](forward-eq.md)
- [The forward algorithm computes the likelihood](likelihood-eq-sum-forward.md)

## Related topics

- [Gibbs sampling leaves the target stationary](../../bayesian-inference-and-sampling/markov-chain-monte-carlo/invariant-gibbs-kernel.md): the full-support coordinate case.
- [Posterior decoding](posterior-path.md): a different operation, maximizing each smoothed marginal rather than sampling a joint path.

## Sources

- M. D. Rasmussen, M. J. Hubisz, I. Gronau and A. Siepel, "Genome-wide inference of ancestral recombination graphs", PLoS Genetics 10(5) (2014), e1004342, <https://doi.org/10.1371/journal.pgen.1004342>, "The threading problem", Figure 3, "Gibbs sampling for single sequences", and Methods ("Stochastic traceback" and "Sampling a recombination threading"); the subtree-Hastings distinction is described in "Subtree sampling". The finite-weight FFBS identity and the block-invariance argument above are derived directly from the canonical forward recursion.
