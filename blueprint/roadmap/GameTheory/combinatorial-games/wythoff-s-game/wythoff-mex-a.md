# The mex sequence of Wythoff's game with terminal positions

Fix a natural number $\ell$.
The sequence $(a_n)_{n \ge 0}$ is defined recursively: $a_n$ is the least natural number greater
than $\ell$ that differs from $a_i$ and from $a_i + i + \ell + 1$ for every $i < n$. Writing
$b_i = a_i + i + \ell + 1$, this says that $a_n$ is the least natural number outside
$\{0, 1, \dots, \ell\} \cup \{a_i, b_i : i < n\}$; in particular $a_0 = \ell + 1$ and
$b_0 = 2\ell + 2$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 17, equation (mexdef) (`jis-2026-26.1.6-thm-17`).
