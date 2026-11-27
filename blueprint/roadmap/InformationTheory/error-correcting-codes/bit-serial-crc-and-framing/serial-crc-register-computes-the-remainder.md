# A bit-serial CRC register computes the remainder

Let $r \in \mathbb{N}$, let $t$ be a width-$r$ binary taps word, and let $M_t = X^r + P_t \in \mathbb{F}_2[X]$ be its monic binary modulus (where $P_t = \sum_{i=0}^{r-1} t_i X^i$ is the binary polynomial of $t$, so $M_t = 1$ when $r = 0$). The zero-initialized, unreflected bit-serial CRC register starts from the zero width-$r$ word $0$ and, on each input bit $b \in \{0, 1\}$, shifts left by one bit within width $r$, XORs with $t$ when $r \ge 1$ and the shifted-out top bit is $1$, and XORs the input bit into bit $0$ (modulo $2^r$). In terms of binary polynomials, each step maps the current state $w$ to $(P_w X + \beta(b)) \bmod M_t$, where $\beta(0) = 0$ and $\beta(1) = 1$.

After any finite bit sequence $B = (b_0, b_1, \dots, b_{n-1}) \in \{0, 1\}^n$ has been read most significant bit first from the zero register, the binary polynomial of the register state $\mathrm{run}_{r, t}(B)$ equals the remainder of the message polynomial $m(B) = \sum_{j=0}^{n-1} \beta(b_j) X^{n-1-j}$ modulo $M_t$:

$$P_{\mathrm{run}_{r, t}(B)} = m(B) \bmod M_t.$$

The formula follows by induction on $n$, since $X(u \bmod M_t) + \beta(b) \equiv X u + \beta(b) \pmod{M_t}$ and each register state represents a polynomial of degree less than $r$.

## Sources

- W. W. Peterson and D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49(1):228–235, 1961.
- S. Lin and D. J. Costello, *Error Control Coding*, 2nd edition, Pearson Prentice Hall, 2004, Chapter 5 (cyclic codes and their shift-register encoders).
