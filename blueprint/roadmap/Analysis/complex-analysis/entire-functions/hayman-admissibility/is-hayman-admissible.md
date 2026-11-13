# Hayman-admissible function (finite radius)

Let $G : \mathbb{C} \to \mathbb{C}$, let
$R_0$ and $\rho$ be real numbers, write $G'$ for the complex derivative of $G$ and $A$, $B$ for
the Hayman auxiliary functions of $G$, and say that a property holds for $r$ near $\rho$ if there
is $\eta > 0$ such that it holds for every $r \in (R_0, \rho)$ with $r > \rho - \eta$. Then $G$ is
Hayman admissible on $(R_0, \rho)$ when $0 < R_0 < \rho$; $G$ is analytic on the open disk
$|z| < \rho$; for every $r \in (R_0, \rho)$, $G(r)$ is a positive real number and
$r\,G'(r)/G(r)$ is real; $A(r) \to \infty$ and $B(r) \to \infty$ as $r$ tends to $\rho$ within
$(R_0, \rho)$; and there is a function $\delta : \mathbb{R} \to \mathbb{R}$ with
$0 < \delta(r) < \pi$ for $r$ near $\rho$ such that for every $\varepsilon > 0$ and all $r$ near
$\rho$, every real $\theta$ with $|\theta| \le \delta(r)$ satisfies the locality estimate

$$\left|G(re^{i\theta}) - G(r)\,e^{i\theta A(r) - \theta^2 B(r)/2}\right|
\le \varepsilon \left|G(r)\,e^{i\theta A(r) - \theta^2 B(r)/2}\right|,$$

and every real $\theta$ with $\delta(r) \le |\theta| < \pi$ satisfies the decay estimate
$|G(re^{i\theta})| \le \varepsilon\,|G(r)|/\sqrt{B(r)}$.

The capture, locality and decay conditions follow the Flajolet-Sedgewick formulation rather than
the abbreviated maximum-modulus restatement (Jiyou Li, "Asymptotic Estimate for the Multinomial
Coefficients", Journal of Integer Sequences 23 (2020), Article 20.1.3, Lemma [Hayman] `lem2`),
whose maximum-modulus condition is insufficient as stated and is not used.
