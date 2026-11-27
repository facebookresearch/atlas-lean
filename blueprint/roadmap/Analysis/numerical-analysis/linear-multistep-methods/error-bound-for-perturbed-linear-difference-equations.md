# Error bound for perturbed linear difference equations

Let $\rho(z) = \alpha_k z^k + \cdots + \alpha_0$, with $\alpha_k \ne 0$, satisfy the [root condition](root-condition.md), and let $\Gamma = \sup_l |\gamma_l|$ be the bound of the [coefficients of $1/(\alpha_k + \alpha_{k-1} z + \cdots + \alpha_0 z^k)$](bounded-coefficients-of-the-reciprocal-polynomial.md). Let $N \ge k$, let $B^*, \Lambda, E \ge 0$ and $\beta > 0$, and let the real numbers $\beta_{j,m}$ and $\lambda_m$ satisfy

$$|\beta_{k,m}| + |\beta_{k-1,m}| + \cdots + |\beta_{0,m}| \le B^*, \qquad |\beta_{k,m}| \le \beta, \qquad |\lambda_m| \le \Lambda \qquad (0 \le m \le N).$$

Let $0 \le h < |\alpha_k| / \beta$. Then every solution $e_0, \dots, e_N$ of

$$\alpha_k e_{m+k} + \alpha_{k-1} e_{m+k-1} + \cdots + \alpha_0 e_m = h\bigl(\beta_{k,m} e_{m+k} + \cdots + \beta_{0,m} e_m\bigr) + \lambda_m \qquad (0 \le m \le N - k)$$

with $|e_s| \le E$ for $s = 0, \dots, k - 1$ satisfies

$$|e_n| \le K^* \exp(n h L^*) \qquad (0 \le n \le N),$$

where $\Gamma^* = \Gamma / (1 - h |\alpha_k|^{-1} \beta)$, $L^* = \Gamma^* B^*$, $A = |\alpha_k| + |\alpha_{k-1}| + \cdots + |\alpha_0|$ and $K^* = \Gamma^* (N\Lambda + AEk)$.

The bound plays the part of the discrete Gronwall lemma for multistep methods: the root condition keeps the solutions of the unperturbed recurrence bounded, and the perturbation terms then grow at most exponentially in $nh$.

## Depends on

- [Root condition](root-condition.md)
- [Bounded coefficients of the reciprocal of a root-stable polynomial](bounded-coefficients-of-the-reciprocal-polynomial.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4.2, Lemma 2 for the difference equation (67) and its proof through (69)–(71). In (67) the last term on the left is printed $\alpha_0 e_0$; the proof uses $\alpha_0 e_m$, as stated here. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
