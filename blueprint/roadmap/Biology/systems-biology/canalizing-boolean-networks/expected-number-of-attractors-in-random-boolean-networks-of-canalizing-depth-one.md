# Expected number of attractors in random Boolean networks of canalizing depth one

Consider a synchronous Boolean network $x \mapsto f(x) = (f_1(x),\dots,f_n(x))$ on $\{0,1\}^n$; an **attractor of length $\ell$** is a cycle of $\ell$ distinct states $a_1 \to a_2 \to \dots \to a_\ell \to a_1$. Draw the network uniformly among all networks whose $n$ update functions each have canalizing depth exactly one (exactly one canalizing layer followed by a noncanalizing core).

Fix $\ell \geq 1$. For $\alpha,\beta \in \{0,1\}^\ell$ let $|\beta|$ be the number of ones, $\bar\alpha$ the componentwise negation and $s(\beta)$ the cyclic shift. Define

$$\phi(\alpha,\beta) = \begin{cases} 2^{-|\beta|}, & \alpha \vee \beta = \beta,\\ 0, & \text{otherwise}, \end{cases} \qquad g(\alpha,\beta) = \tfrac14\bigl(\phi(\alpha,\beta) + \phi(\bar\alpha,\beta) + \phi(\alpha,\bar\beta) + \phi(\bar\alpha,\bar\beta)\bigr),$$

and the $2^\ell \times 2^\ell$ matrix $(G_\ell)_{a,b} = g(a, s(b))$, indexing rows and columns by binary strings of length $\ell$. Let $P_{G_\ell}(t) = \det(tI - G_\ell)$.

**Theorem.** The expected number $A_{\ell,n}$ of attractors of length $\ell$ converges as $n \to \infty$ to

$$A_\ell = \frac{1}{\ell\, P_{G_\ell}'(1)} .$$

Numerically $A_1 = 1$, $A_2 = 2/3$, $A_3 = 64/189$, $A_4 \approx 0.2856$, $A_5 \approx 0.2004$, $A_6 \approx 0.1721$. The same limits hold for a random network built from canalizing functions of any positive depth with probability proportional to the product of the numbers of canalizing variables, because depth-one functions dominate. For a uniformly random Boolean network with no canalization constraint the expected number of attractors of length $\ell$ is exactly $1/\ell$; since $|P_{G_\ell}'(1)| < 1$ for $\ell > 1$, a large depth-one network has on average **more short cycles** than an unconstrained one, although simulations show it has fewer attractors and much smaller attractors overall.

## Depends on

- [Canalizing depth and the layer decomposition of Boolean functions](canalizing-depth-and-the-layer-decomposition-of-boolean-functions.md)
## Expansion

The matrix $G_\ell^{\top}$ is column-stochastic: for each $\beta$, $\sum_\alpha \phi(\alpha,\beta) = \sum_{k} \binom{|\beta|}{k} 2^{-|\beta|} = 1$; it is irreducible because $g(\alpha,0)$ and $g(0,\alpha)$ are positive, so $1$ is a simple eigenvalue and $P_{G_\ell}(t) = (1-t)Q(t)$ with $Q(1) \neq 0$. The entry $g(a,s(b))$ is the probability that a single random depth-one update function maps a length-$\ell$ trajectory pattern of its inputs to the shifted output pattern. Summing over how the $n$ coordinates distribute among the $2^\ell$ column patterns gives the multinomial sum $C_n = \sum_{|m| = n} (G_\ell m)^m n^{-n}$. A MacMahon-type identity, the substitution $x = y(z)$ with $y = -W(-z)$ (Lambert $W$), and singularity analysis at $z = 1/e$ give $C_n \to -1/Q(1) = 1/P_{G_\ell}'(1)$; dividing by $\ell$ removes the cyclic relabelings of a cycle. Sequences with repeated states contribute $o(1)$ because the corresponding principal submatrices are strictly substochastic. For $\ell = 2$ one computes $P_{G_2}(t) = t^4 - \tfrac54 t^3 + \tfrac14 t^2$, so $P_{G_2}'(1) = 3/4$ and $A_2 = 2/3$.

## Sources

- E. Paul, G. Pogudin, W. Qin, R. Laubenbacher, "The dynamics of canalizing Boolean networks", *Complexity* 2020 (2020) 3687961. Section 7, Theorem 2 with Eqs. (12)–(15), Remarks 5–6; Appendix A, Lemmas A.1–A.3 and Corollary A.1. <https://doi.org/10.1155/2020/3687961>. PMCID: PMC10399297.
