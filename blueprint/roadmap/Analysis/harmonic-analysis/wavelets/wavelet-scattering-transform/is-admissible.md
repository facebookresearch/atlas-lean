# Admissible scattering wavelet in dimension one

A scattering wavelet $\psi$ (with low-pass $\varphi$) is admissible (S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), Theorem 2.6, conditions (29)–(30), with $d = 1$ and $G = \{1, -1\}$) if it satisfies the [standing assumptions](is-scattering-wavelet.md) and there are $\eta \in \mathbb{R}$ and an integrable $\rho \ge 0$ with $|\hat\rho(\omega)| \le |\hat\varphi(2\omega)|$ and $\hat\rho(0) = 1$ such that

$$\alpha = \inf_{1 \le |\omega| \le 2} \sum_{j \in \mathbb{Z}} \sum_{r = \pm 1} \hat\Psi(2^{-j} r \omega)\, |\hat\psi(2^{-j} r \omega)|^2 > 0,$$

where $\hat\Psi$ is the [admissibility function](admissibility-function.md). The definition adds two conditions that make the series meaningful: the series defining $\hat\Psi$ converges at every $\omega$ (its terms are nonnegative, since $|\hat\rho| \le 1$ under the standing assumptions), and the lower bound $\alpha$ is required of sums over $\mathbb{Z}$ that converge unconditionally. **Satisfiability (numerical).** Mallat (Section 2.3, the remark after the proof of Theorem 2.6) reports that the analytic cubic-spline Battle–Lemarié wavelet is admissible in dimension one with $\eta = 3\pi/2$, choosing for $\rho$ a positive cubic box spline; a numerical evaluation of (30) gives $\alpha = 0.2766 > 0$. Explicitly, with $\psi_{BL}, \varphi_{BL}$ the cubic-spline Battle–Lemarié wavelet and scaling function:
- $\hat\psi = \sqrt2\, |\hat\psi_{BL}|\, \mathbf{1}_{\omega > 0}$ and $\hat\varphi(\omega) = \hat\varphi_{BL}(\omega/2)$; both are real, and (9) with $\beta = 1/2$ follows from the identities $\sum_j |\hat\psi_{BL}(2^j\omega)|^2 = 1$ and $|\hat\varphi_{BL}(\omega)|^2 + |\hat\psi_{BL}(\omega)|^2 = |\hat\varphi_{BL}(\omega/2)|^2$ of the Battle–Lemarié basis;
- $\rho$ the centred cubic B-spline, $\hat\rho(\omega) = \operatorname{sinc}^4(\omega/2)$, so $\hat\rho(0) = 1$ and $|\hat\rho(\omega)| \le \hat\varphi_{BL}(\omega) = |\hat\varphi(2\omega)|$;
- $\eta = 3\pi/2$.

For this choice the series defining $\hat\Psi$ converges ($\rho$ has finite variance), and the sums in (30) converge absolutely ($|\hat\Psi|$ grows at most like $\log^2|\omega|$, while $|\hat\psi|^2$ decays like $|\omega|^{-8}$ at infinity and vanishes to order $8$ at $0$), so the two side conditions hold. These are numerical checks, not proofs.
