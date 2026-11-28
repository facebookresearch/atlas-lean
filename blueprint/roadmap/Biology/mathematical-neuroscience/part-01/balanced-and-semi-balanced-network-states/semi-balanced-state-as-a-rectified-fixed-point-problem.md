# Semi-balanced state as a rectified fixed-point problem

**Setting.** As in the mean-field rate model $\tau\dot r = -r + f(\overline{JK}[Wr + X])$ with effective connectivity $W$ ($n \times n$) and external input $X$, write $[\cdot]_+$ for the entrywise positive part.

**Definition (semi-balanced state).** A rate vector $r \in \mathbb R^n$ is semi-balanced if for every population $a$:

1. $[Wr + X]_a \le 0$ (no excess excitation);
2. if $[Wr + X]_a < 0$ then $r_a = 0$ (populations with excess inhibition are silenced);
3. $r_a \ge 0$.

Equivalently, populations with positive rates form a balanced sub-network ($[Wr+X]_a = 0$ whenever $r_a > 0$): a linear complementarity condition $r \ge 0$, $-(Wr + X) \ge 0$, $r^\top(Wr + X) = 0$.

**Theorem 1 (fixed-point form).** $r$ is semi-balanced if and only if

$$[\,Wr + X + r\,]_+ = r .$$

Moreover, for every $c > 0$, $[Wr + X + r]_+ = r$ holds if and only if $[Wr + X + c\,r]_+ = c\,r$, so mixing quantities with units of rate and of input current is harmless.

**Theorem 2 (bounded rates imply semi-balance).** Let $W, X$ be fixed and suppose that for all large $\overline{JK}$, $I = \overline{JK}[Wr + X]$ and $r = f(I)$ with $f$ non-negative, non-decreasing, $\lim_{x \to -\infty} f(x) = 0$ and $\lim_{x\to\infty} f(x) = M \in (0, \infty]$. If $r^\infty = \lim_{\overline{JK}\to\infty} r$ exists with $r^\infty_a < M$ for all $a$, then

$$[\,W r^\infty + X + r^\infty\,]_+ = r^\infty .$$

Conversely the semi-balanced state is the large-coupling limit of networks whose rates stay $O(1)$.

## Depends on

- [Breakdown of the classical balanced state](breakdown-of-the-classical-balanced-state.md)

## Expansion

For Theorem 1, if $r_a > 0$ the positive part is active, so $r_a = [Wr+X]_a + r_a$ and $[Wr+X]_a = 0$; if $r_a = 0$ then $[Wr+X]_a^+ = 0$, i.e. $[Wr+X]_a \le 0$; the converse checks the two cases directly, and the scaling statement follows because the case analysis never uses the value of $r_a > 0$. For Theorem 2, let $c = \lim I_a/\overline{JK} = [Wr^\infty + X]_a$; if $c > 0$ then $I_a \to \infty$ and $r_a \to M$, contradicting $r^\infty_a < M$; if $c < 0$ then $I_a \to -\infty$ and $r^\infty_a = 0$; and $c = 0$ is balance. Because the solution set of $[Wr+X+r]_+ = r$ changes as different populations are silenced, $r$ is a continuous piecewise linear function of $X$, like the hidden layer of a ReLU network; this gives semi-balanced spiking networks nonlinear stimulus representations, which in simulation improve linear decoding of hand-written digits.

## Sources

- C. Baker, V. Zhu, R. Rosenbaum, "Nonlinear stimulus representations in neural circuits with approximate excitatory-inhibitory balance", PLoS Computational Biology 16 (2020) e1008192, Results (semi-balanced state, Eq. 4) and Methods (Theorems 2–4 with proofs, Eqs. 6–8), <https://doi.org/10.1371/journal.pcbi.1008192> (PMC7526938).
