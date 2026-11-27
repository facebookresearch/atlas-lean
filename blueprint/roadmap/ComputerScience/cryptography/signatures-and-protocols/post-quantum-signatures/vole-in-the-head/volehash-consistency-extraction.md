# Extraction from the VOLEHash consistency check

Let $\mathcal{H} \subseteq \mathbb{F}^{k \times \ell}$ be an $\epsilon$-almost universal hash family ($\Pr_{H \leftarrow \mathcal{H}}[H x = 0] \le \epsilon$ for every nonzero $x \in \mathbb{F}^\ell$), and let $S \subseteq \mathbb{F} \times \mathbb{F}^\ell$ be a set of possible openings $(\Delta, q)$ fixed before $H$ is drawn. There is a map $E_{\mathrm{KOS},S}$, the affine-line extractor, sending $(H, \tilde u, \tilde v) \in \mathbb{F}^{k\times\ell} \times \mathbb{F}^k \times \mathbb{F}^k$ to a line $(u, v) \in \mathbb{F}^\ell \times \mathbb{F}^\ell$, such that the probability over $H$ that some $\tilde u, \tilde v$ and some $(\Delta, q) \in S$ satisfy $H q = \tilde u \Delta + \tilde v$ (the opening passes the KOS-style consistency check) but $q \ne u\Delta + v$ for $(u, v) = E_{\mathrm{KOS},S}(H, \tilde u, \tilde v)$ is at most

$$
\epsilon\binom{|S|}{2} + \epsilon\binom{|S|}{3} \le \frac{\epsilon\,|S|^3}{6}.
$$

The first term bounds a *bad pair*, two distinct openings $(\Delta, q_0), (\Delta, q_1) \in S$ with $H q_0 = H q_1$; the second bounds a *bad triple*, three openings with distinct $\Delta_i$ that are not collinear in $\mathbb{F}^{1+\ell}$ while $(\Delta_i, H q_i)$ are collinear in $\mathbb{F}^{1+k}$. In FAEST's VOLE-in-the-head proof the set is the response graph $S_t = \{(\Delta, \mathrm{Resp}_t(\Delta))\}$ of a commitment attempt $t$, fixed before the challenge: since $S_t$ is the graph of a function, bad pairs are impossible, and VOLEHash is $\varepsilon_v$-almost universal with $\varepsilon_v = 2^{-4\lambda}(1 + 2^{-4})$ (under its input-length condition), so extraction for that attempt fails with probability at most $\varepsilon_v\binom{|S_t|}{3}$, where $|S_t| \le 2^{\lambda - w_{\mathrm{grind}}}$.

## Proof sketch

A bad pair or a bad triple requires $H$ to vanish on a fixed nonzero vector, which has probability at most $\epsilon$; union bound over the at most $\binom{|S|}{2}$ pairs and $\binom{|S|}{3}$ triples. If neither occurs, all passing openings have distinct $\Delta$, and any two of them determine the same line through all of them, which the extractor outputs.

## Depends on

- [VOLE-in-the-head](vole-in-the-head.md)
- [Universal hash family](../../../../data-structures/hashing/universal-hashing/is-universal.md)

## Sources

- Carsten Baum et al., "FAEST v3: Algorithm Specifications", FAEST Team, 2026.
