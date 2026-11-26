# Canonical sequential realization of a profile

Let $(\pi_k)_{k \ge 1}$ be a sequence of
nonnegative integers with partial sums $\Pi_k = \sum_{1 \le j \le k} \pi_j$. For $i \ge 1$ let
$k(i)$ be the least $k \ge 0$ with $i \le \Pi_k$, or $0$ if there is none, and let
$p_1 = 2, p_2 = 3, \dots$ be the primes in increasing order. The canonical sequential realization
$H_{\mathrm{seq}}$ of $\pi$ is the function $\mathbb{N} \to \mathbb{N}$ that sends $m \ge 1$ to
$\sum_{i \ge 1} a_i\, k(i)$, where $a_i$ is the exponent of $p_i$ in $m$, and sends $0$ to $0$;
thus $H_{\mathrm{seq}}$ is completely additive with $H_{\mathrm{seq}}(p_i) = k(i)$.

## Sources

- Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116, Definition 2 (canonical sequential realization, Section 7.2).
