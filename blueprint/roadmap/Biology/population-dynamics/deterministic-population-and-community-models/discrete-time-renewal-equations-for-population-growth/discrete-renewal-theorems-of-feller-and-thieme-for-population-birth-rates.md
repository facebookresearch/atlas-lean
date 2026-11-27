# Discrete renewal theorems of Feller and Thieme for population birth rates

**Scalar renewal equation.** Let $b(t)$ be the number of births at time $t \in \mathbb N$ and $k(s)$ the expected number of offspring produced at age $s \ge 1$ by an individual born at time $0$. Births satisfy

$$b(t) = \sum_{s=1}^t k(s)\,b(t-s) + g(t), \qquad t \in \mathbb N, \quad b(0) = g(0),$$

where $g(t) \ge 0$ collects births from individuals present before time $0$. Assume

- A1: $k(t) \ge 0$ for all $t$, with strict inequality for some $t$;
- A2: $\mathcal R_0 = \sum_{t\ge1} k(t) < \infty$ (the basic reproduction number: expected lifetime offspring);
- A3: $\{k(t)\}$ is not periodic (the gcd of the ages with $k(t) > 0$ is $1$).

With the $z$-transform $\bar k(z) = \sum_{s\ge1} k(s)z^{-s}$, the Euler–Lotka equation is $\bar k(z) = 1$; for $\mathcal R_0 > 1$ it has a unique real root $\rho > 1$ (the asymptotic growth factor per time step).

**Theorem (Feller).** Under A1–A3, with $g \ge 0$ and $\sum_t g(t) < \infty$:
1. If $\mathcal R_0 < 1$: $b(t) \to 0$ and $\sum_{t\ge0} b(t) = \bar g(1)/(1 - \mathcal R_0)$.
2. If $\mathcal R_0 = 1$: $b(t) \to \bar g(1)\big/\sum_{s\ge1} s\,k(s)$, the ratio of the initial input to the mean generation time.
3. If $\mathcal R_0 > 1$: $\rho^{-t}b(t) \to \bar g(\rho)\big/\sum_{s\ge1} s\,k(s)\rho^{-s}$.

**Theorem (Thieme, systems).** For a vector of births by birth state $B(t)$ with non-negative matrix kernel $K(s)$ and input $G(t)$, $B(t) = \sum_{s=1}^t K(s)B(t-s) + G(t)$, under the irreducibility and aperiodicity assumptions A4–A7 and $\|G(t)\| \le M$: if $\mathcal R_0 = r(\bar K(1)) \ge 1$, the Euler–Lotka condition "$\bar K(\rho)$ has spectral radius $1$" has a unique real solution $\rho$ with $1 < \rho < \mathcal R_0$ or $\rho = 1 = \mathcal R_0$, and

$$\rho^{-t}B(t) \to c\,\Phi, \qquad c = \frac{\Psi\,\bar G(\rho)}{\Psi\big(\sum_{s\ge1} s\rho^{-s}K(s)\big)\Phi},$$

where $\Phi$ ($\|\Phi\| = 1$) and $\Psi$ ($\Psi\Phi = 1$) are the right and left positive eigenvectors of $\bar K(\rho)$ for eigenvalue $1$. Thus the birth-state composition converges to $\Phi$, the stable birth-state distribution, and $\Psi$ weights initial contributions by their reproductive value.

## Depends on

- [Discrete Euler–Lotka equation](../../leslie-matrix-model/sum-fertility-mul-survivorship-div-pow-e.md)

## Proof sketch

Taking $z$-transforms turns the convolution into $\bar b(z) = \bar g(z)/(1 - \bar k(z))$. Since $\bar k$ is strictly decreasing on $(0,\infty)$ for real $z$, with $\bar k(1) = \mathcal R_0$ and $\bar k(z) \to 0$ as $z \to \infty$, there is exactly one real root $\rho$, and $\rho > 1 \iff \mathcal R_0 > 1$. Aperiodicity makes $\rho$ the unique root of modulus $\ge \rho$, so the asymptotics are governed by the simple pole of $\bar b$ at $z = \rho$, which gives $\rho^{-t}b(t) \to \bar g(\rho)/(-\rho\bar k'(\rho))$ with $-\rho\bar k'(\rho) = \sum_s s\,k(s)\rho^{-s}$. In the system case the Perron–Frobenius eigenvalue of $\bar K(z)$ plays the role of $\bar k(z)$ and the residue is a rank-one projection $\Phi\Psi$. The renewal formulation needs only birth states, typically far fewer than the individual states of a matrix (Leslie-type) model, and yields $\mathcal R_0$ directly.

## Related topics

- [Euler–Lotka equation and the reproduction number](../../../epidemiology/euler-lotka-equation-and-the-reproduction-number/README.md)

## Sources

- B. Boldin, O. Diekmann and J. A. J. Metz, "Population growth in discrete time: a renewal equation oriented survey", *Journal of Difference Equations and Applications* 30 (2024), 1062–1090, <https://doi.org/10.1080/10236198.2023.2265499>. Preprint version: arXiv:2306.09193 (2023), assumptions A1–A3, Euler–Lotka equation, Feller's renewal theorem and Thieme's renewal theorem for systems, <https://doi.org/10.48550/arXiv.2306.09193>.
