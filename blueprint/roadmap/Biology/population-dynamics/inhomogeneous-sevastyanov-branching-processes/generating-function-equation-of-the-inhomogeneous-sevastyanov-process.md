# Generating-function equation of a time-inhomogeneous Sevast'yanov branching process

**Model (symmetric branching tree).** A branch born at time $\tau \ge 0$ lives for a random time $L \sim \mu_\tau$ on $(0,\infty]$; at the end of its life, given $L = \ell$, it splits into $N$ new branches, all born at time $\tau + \ell$, with $N \mid L = \ell \sim \nu_{\tau,\ell}$ on $\mathbb{N}_0$, and these evolve independently by the same rules. Let $h_{\tau,\ell}(s) = \sum_k \nu_{\tau,\ell}(k)s^k$ be the offspring generating function, $Z(t)$ the number of branches alive at time $t \ge \tau$ (the Sevast'yanov process born at $\tau$), $F_\tau(s;t) = \mathbb{E}_\tau[s^{Z(t)}]$ and $p^0_\tau(t) = \mathbb{P}_\tau(Z(t) = 0)$. Assume the regularity condition under which $\mathbb{E}_\tau Z(t) < \infty$ for all $t$.

**Theorem.** On $\{0 \le \tau \le t\}$, $F_\tau(s;t)$ is the unique bounded solution of

$$F_\tau(s;t) = s^{\mathbf{1}\{t > \tau\}}\,\mu_\tau\big([t - \tau, \infty)\big) + \int_{[0, t-\tau)} h_{\tau,\ell}\big(F_{\tau+\ell}(s;t)\big)\,\mu_\tau(d\ell),$$

and the finite-time extinction probability is the unique bounded solution of

$$p^0_\tau(t) = \mathbf{1}\{t = \tau\} + \int_{[0,t-\tau)} h_{\tau,\ell}\big(p^0_{\tau+\ell}(t)\big)\,\mu_\tau(d\ell).$$

In the asymmetric version, where a reproducing branch continues with its age (one child keeps the parent's age, the others start at age $0$), the same equations hold with $h_{\tau,\ell}$ replaced by a bivariate generating function $\tilde h_{\tau,\alpha,\ell}(x, y)$ evaluated at $(F_{\tau+\ell,\alpha+\ell}, F_{\tau+\ell,0})$; such processes include a broad class of inhomogeneous Crump–Mode–Jagers processes.

## Depends on

## Expansion

Condition on the first branch: if it is still alive at $t$ (probability $\mu_\tau([t-\tau,\infty))$) it contributes one branch; otherwise it died at age $\ell < t - \tau$ and produced $N$ independent copies born at $\tau + \ell$. The branching property of the tree gives $\mathbb{E}[\prod_{k \le N} s^{Z_k(t)} \mid L, N] = F_{\tau+\ell}(s;t)^N$, and averaging over $N$ yields $h_{\tau,\ell}(F_{\tau+\ell})$. Uniqueness follows because the right-hand side is a contraction on bounded functions over small time windows, iterated over $[\tau, t]$. Setting $s = 0$ gives the extinction equation.

## Sources

- F. M. Andersen, M. A. Suchard, C. Wiuf and S. Bhatt, "Inhomogeneous branching trees with symmetric and asymmetric offspring and their genealogies", arXiv:2510.07921 (2025), Propositions 2.1, 2.2, 3.6, Theorem 3.7 and Corollaries 3.9, 3.10, <https://doi.org/10.48550/arXiv.2510.07921>.
