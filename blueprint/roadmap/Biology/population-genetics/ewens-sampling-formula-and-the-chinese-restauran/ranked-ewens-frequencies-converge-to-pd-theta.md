# Almost-sure l1 convergence of nested Ewens frequencies to GEM and PD

Fix $\theta>0$ and use one nested CRP coupling. Pad its block sizes in
order of appearance with zeros and write $p^{(n)}_k=N_{n,k}/n$ for
$n\ge1$. On this space there are independent
$W_k\sim\operatorname{Beta}(1,\theta)$, $k\ge1$, such that, for
$P_k=W_k\prod_{j<k}(1-W_j)$,

$$p^{(n)}_k\longrightarrow P_k\ \text{for every }k\quad\text{and}\quad
 \sum_{k\ge1}|p^{(n)}_k-P_k|\longrightarrow0
 \qquad\text{almost surely}.$$

The law of $P$ is GEM$(\theta)$ and $\sum_kP_k=1$ almost surely.
Writing $p^\downarrow$ for decreasing rearrangement, the ranked vectors
also converge almost surely in $\ell^1$ to $P^\downarrow$.
The latter law is PD$(\theta)$, also written PD$(0,\theta)$.
Here PD is defined as the decreasing rearrangement of GEM.
No equivalence with a gamma-process construction is needed as a premise.

## Depends on

- [CRP marginal laws](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp.md)

## Proof depends on

- [First-block Beta limit and membership construction](size-biased-allele-frequency-in-an-ewens-sample.md)
- [Stick-breaking weights sum to one](../../../Probability/bayesian-statistics/dirichlet-process/ae-has-sum-weight.md)

## Expansion

Separate each seating decision into first-block membership and, when it
is outside that block, a decision in the residual restaurant.
The outside probability is $(n-J_n+\theta)/(n+\theta)$; conditional on
being outside, a new residual block has probability
$\theta/(n-J_n+\theta)$ and an existing residual block of size $m$ has
probability $m/(n-J_n+\theta)$.
Independent uniform streams therefore realize the membership urn and an
independent residual CRP. Its number of customers tends to infinity
because the first-block limit is strictly less than one almost surely.
Repeat the construction in the residual restaurant. Induction gives
independent Beta breaks and coordinatewise convergence, simultaneously
for all coordinates by a countable intersection of probability-one events.
The residual stick has expectation $(\theta/(1+\theta))^k\to0$,
so the linked mass-one result applies. The GEM and PD laws and the fact
that GEM weights sum to one almost surely are taken as given.

For any nonnegative mass-one vectors $x_n,x$ with coordinatewise
convergence, choose a finite prefix whose $x$ tail has mass below
$\varepsilon$. The prefix error tends to zero and the $x_n$ tail mass
tends to the $x$ tail mass. Splitting the $\ell^1$ norm into prefix and
tails proves $\|x_n-x\|_1\to0$.
Ranking is a contraction: for $t>0$ the counts
$N_x(t)=\#\{i:x_i>t\}$ are finite, and layer-cake/Tonelli gives

$$\|x^\downarrow-y^\downarrow\|_1
 =\int_0^\infty|N_x(t)-N_y(t)|\,dt
 \le\sum_i\int_0^\infty
 |\mathbf1_{x_i>t}-\mathbf1_{y_i>t}|\,dt
 =\|x-y\|_1.$$

Apply this to $p^{(n)},P$ to obtain ranked convergence.
This almost-sure statement uses the nested coupling; for uncoupled
samples specified only by their Ewens marginal laws, the conclusion
asserted is convergence in distribution in $\ell^1$.

## Sources

- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Definition 1.3 and Theorem 1.5. The independent residual construction, l1 argument and ranking contraction are explicit above.
