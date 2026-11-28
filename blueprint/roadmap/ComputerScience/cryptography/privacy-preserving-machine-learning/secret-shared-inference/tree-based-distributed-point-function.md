# A two-party distributed point function from a pseudorandom generator

If $G:\{0,1\}^\lambda\to\{0,1\}^{2(\lambda+1)}$ is a nonuniformly secure PRG and the group conversion is pseudorandom, the Boyle–Gilboa–Ishai construction is a two-party DPF for point functions $\{0,1\}^n\to\mathbb{G}$ with keys of $n(\lambda+2)+\lambda+\lceil\log_2|\mathbb{G}|\rceil$ bits.

Key generation makes at most $2(n+\lceil\log|\mathbb{G}|/(\lambda+2)\rceil)$ PRG calls and evaluation at most $n+\lceil\log|\mathbb{G}|/(\lambda+2)\rceil$. The construction is the scheme $(\mathrm{Gen}^\bullet,\mathrm{Eval}^\bullet)$ of the source's Figure 1, using its conversion $\mathrm{Convert}$ (Figure 3) from strings to elements of a finite Abelian group $\mathbb{G}$ in the representation of the [FSS definition](function-secret-sharing.md). The two keys share the same correction words; party $b$'s evaluation outputs $(-1)^b\big(\mathrm{Convert}(s^{(n)})+t^{(n)}\cdot CW^{(n+1)}\big)$, the sign applying to the whole converted-plus-correction term, so the two outputs sum to $f_{\alpha,\beta}(x)$. Both $G$ and $\mathrm{Convert}$ are assumed pseudorandom against nonuniform adversaries (the source's proof is concrete: $(T,\varepsilon)$-security against size-$T$ adversaries), and key secrecy holds against nonuniform distinguishers, with $n$ and $\log|\mathbb{G}|$ polynomial in $\lambda$.

## Depends on

- [Function secret sharing and distributed point functions](function-secret-sharing.md)
- [Asymptotic PRG security relative to a class of distinguishers](../../symmetric-key/pseudorandom-generators/prgsecure.md)

## Proof depends on

None.

## Expansion

Not ready: the expansion must add defining pages for $\mathrm{Gen}^\bullet$, $\mathrm{Eval}^\bullet$ and $\mathrm{Convert}$, and the proof (Claims 3.5–3.8) needs, besides PRG security, a game-hopping argument in which each step replaces the expansion of the seed hidden from the single key by a random string, conditional on the earlier steps, and a final step (Claim 3.8) replacing $\mathrm{Convert}$ applied to a fresh uniform leaf seed by a uniform group element, conditional on the preceding hybrid; that $\mathrm{Convert}$ is pseudorandom (with enough stretch and negligible modular bias for non-power-of-two group sizes) is a separate obligation. The reductions hardwire $(j,b,\alpha,\beta)$, which is why nonuniform security is assumed.

## Sources

- Elette Boyle, Niv Gilboa, Yuval Ishai, "Function Secret Sharing: Improvements and Extensions", ACM CCS 2016, DOI 10.1145/2976749.2978429; numbers from the full version, IACR ePrint 2018/707, read in the [author-hosted copy](https://tzin.bgu.ac.il/~gilboan/publications/FSS-CCS-full.pdf): §3.2.2, Theorem 3.3 and Figure 1 (pp. 9–10), Claims 3.5–3.8 (Claim 3.8 on p. 14), Figure 3 (p. 16) (in this version the root control bits are fixed deterministically, one bit fewer than the conference version).
