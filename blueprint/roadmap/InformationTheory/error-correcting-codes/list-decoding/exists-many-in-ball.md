# List-decoding capacity, converse

Let $\alpha$ be an alphabet with $q \ge 2$ letters, let $0 < \rho < 1 - 1/q$ and $\varepsilon > 0$.
For all large enough $n$, every code $C \subseteq \alpha^n$ with at least
$q^{(1 - H_q(\rho) + \varepsilon) n}$ codewords has a Hamming ball of radius $\rho n$ containing at
least $q^{\varepsilon n / 2}$ codewords. So a code of rate $1 - H_q(\rho) + \varepsilon$ that is
list decodable from $\rho n$ errors needs lists of size at least $q^{\varepsilon n / 2}$.

This is Theorem 7.4.1 (ii) (equivalently Theorem 7.4.2 (ii)) of Guruswami, Rudra and Sudan, which
states $L \ge q^{\Omega(\varepsilon n)}$; the constant in $\Omega$ is taken here to be $1/2$. The
proof is theirs: a ball with a uniformly random centre holds $|C| \mathrm{Vol}_q(n, \rho n) / q^n$
codewords on average, and $\mathrm{Vol}_q(n, \rho n) \ge q^{H_q(\rho) n - \varepsilon n / 2}$ for large $n$.
In the statement $q^x$ is written $\exp(x \log q)$, and $H_q(\rho) \log q$ is
$\rho \log(q-1) - \rho \log \rho - (1-\rho)\log(1-\rho)$. Together with [achievability](exists-encoding-list-decodable.md) it shows
that the list-decoding capacity is $1 - H_q(\rho)$.

## Informally uses

- [Some ball holds many codewords](exists-mul-card-filter-ge.md): the averaging over a random centre, equations (7.14)–(7.16).
- [Volume of a Hamming ball, entropy lower bound](../bounds-on-code-size/sum-choose-mul-pow-ge-exp.md): equation (7.13).

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorems 7.4.1 and 7.4.2 (ii), equations (7.12)–(7.17).
