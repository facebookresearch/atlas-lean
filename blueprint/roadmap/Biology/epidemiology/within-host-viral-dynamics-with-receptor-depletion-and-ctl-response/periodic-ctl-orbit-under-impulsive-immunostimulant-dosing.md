# Periodic CTL orbit under impulsive immunostimulant dosing

**Setting.** In the [receptor-dependent within-host model with a CTL response](receptor-dependent-within-host-reproduction-number-with-ctl-response.md), an immunostimulant drug is given at times $t_k = k\tau$ ($k \in \mathbb{N}$, period $\tau > 0$) and raises the CTL level by a fixed amount $\omega > 0$ at each dose: $C(t_k^+) = C(t_k^-) + \omega$, with the continuous dynamics unchanged between doses. Without infection ($I \equiv 0$) the CTL equation is

$$C'(t) = -d_c C(t) \quad (t \ne t_k), \qquad C(t_k^+) = C(t_k^-) + \omega .$$

**Proposition.**

1. This impulsive system has a unique positive $\tau$-periodic solution

$$\tilde C(t) = \frac{\omega\, e^{-d_c (t - t_k)}}{1 - e^{-d_c \tau}}, \qquad t_k < t \le t_{k+1},$$

oscillating between $C_{\min} = \omega e^{-d_c\tau}/(1 - e^{-d_c\tau})$ just before a dose and $C_{\max} = \omega/(1 - e^{-d_c\tau})$ just after, with period average $\omega/(d_c \tau)$.
2. Every solution converges to it: $C(t) - \tilde C(t) = \big(C(0^+) - \tilde C(0^+)\big) e^{-d_c t}$. Starting from no CTLs, the post-dose levels are $C(t_k^+) = \omega (1 - e^{-k d_c \tau})/(1 - e^{-d_c \tau})$ for the $k$-th dose.
3. The infection-free periodic orbit $(\lambda_1/d_T, 0, 0, \lambda_2/d_E, \tilde C)$ is locally asymptotically stable if and only if the monodromy matrix of the $\tau$-periodic linear system

$$I' = \beta T_0 E_0 V - \big(d_I + p\tilde C(t)\big) I, \qquad V' = m d_I I - d_V V$$

has spectral radius below $1$. By comparison, with $R_0 = m\beta T_0 E_0/d_V$, it is stable if $R_0\, d_I/(d_I + p C_{\min}) < 1$ and unstable if $R_0\, d_I/(d_I + p C_{\max}) > 1$.

## Depends on

- [Receptor-dependent within-host reproduction number with a CTL response](receptor-dependent-within-host-reproduction-number-with-ctl-response.md)

## Expansion

Between doses $C$ decays exponentially, so the post-dose values obey the affine recursion $x_{k+1} = x_k e^{-d_c\tau} + \omega$, whose unique fixed point $\omega/(1 - e^{-d_c\tau})$ is globally attracting with contraction factor $e^{-d_c \tau}$; this gives items 1–2. In item 3, $T$ and $E$ decouple from $C$ when $I = V = 0$, and the linearization at the orbit is block triangular: the $T$, $E$ and $C$ directions have Floquet multipliers $e^{-d_T\tau}$, $e^{-d_E\tau}$, $e^{-d_c\tau} < 1$, so stability is decided by the $(I, V)$ block. That block is cooperative (off-diagonal entries $\beta T_0 E_0, m d_I \ge 0$) and its coefficient matrix lies entrywise between the constant matrices obtained with $C_{\max}$ and $C_{\min}$ in place of $\tilde C(t)$; for cooperative linear systems this ordering passes to solutions, and the constant systems are stable exactly when their next-generation numbers $R_0 d_I/(d_I + pC)$ are below $1$. The source states a sufficient condition $\tilde R_0 < 1$ (Theorem 4, Eqs. (28)–(29)) from a Floquet computation that treats the time-dependent $(I, V)$ block as if it could be integrated entrywise; the comparison bounds above are derived here instead.

## Sources

- A. N. Chatterjee, F. Al Basir, "A model for SARS-CoV-2 infection with treatment", *Computational and Mathematical Methods in Medicine* 2020 (2020) 1352982, Section 4: impulsive model (3), Eqs. (18)–(23), Lemma 4 and Eq. (27) (where the printed initial value should read $\tilde C(0^+) = \omega/(1 - e^{-d_c\tau})$), Theorem 4. <https://doi.org/10.1155/2020/1352982> (PMC7463400).
