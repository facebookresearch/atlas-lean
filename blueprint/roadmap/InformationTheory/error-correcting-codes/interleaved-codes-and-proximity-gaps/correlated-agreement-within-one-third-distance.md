# Correlated agreement for random lines within one third of the minimum distance

Let $\mathbb{F}_q$ be a finite field, $C \subseteq \mathbb{F}_q^n$ a linear code of minimum distance $d$, and $e$ an integer with $0 \le e \le \lfloor (d - 1)/3 \rfloor$, so that $3e < d$. Write $\Delta(w, C)$ for the Hamming distance from a word $w$ to $C$. If $u_0, u_1 \in \mathbb{F}_q^n$ satisfy

$$
\Pr_{r \in \mathbb{F}_q}\big[\Delta\big((1 - r)\,u_0 + r\,u_1,\ C\big) \le e\big] > \frac{e + 1}{q},
$$

that is, more than $e + 1$ values $r \in \mathbb{F}_q$ make $(1 - r)u_0 + r u_1$ lie within Hamming distance $e$ of $C$, then $u_0, u_1$ have $e$-correlated agreement with $C$.

## Proof sketch

Pick two good parameters $r_0^* \ne r_1^*$ and pass to $u'_b = (1 - r_b^*)u_0 + r_b^* u_1$, which span the same line and are each $e$-close to codewords $v'_0, v'_1$. If the pair $(u'_0, u'_1)$ had no correlated agreement, the union of the two error sets would have more than $e$ positions. At each such position $j$ the line and the codeword line $(1 - r)v'_0 + r v'_1$ agree for at most one $r$, and positions outside the intersection of the two error sets can only agree at $r = 0$ or $r = 1$, so at most $e + 1$ parameters $r$ make the two lines agree off the error union. For every good $r$ the codeword near the point of the line lies within $3e < d$ of $(1 - r)v'_0 + r v'_1$, so it equals it; hence every good $r$ is one of those at most $e + 1$ parameters, a contradiction. Correlated agreement of $(u'_0, u'_1)$ transfers to $(u_0, u_1)$ by the same affine change of parameters.

The following forms are derived here and are not stated in the cited sources. Applying the statement to the pair $(u_0, u_0 + u_1)$, whose line is $r \mapsto u_0 + r u_1$, shows that more than $e + 1$ scalars $z$ with $u_0 + z u_1$ $e$-close to $C$ already give $e$-correlated agreement of $u_0, u_1$. Since correlated agreement makes every point of the line $e$-close, for every pair either at most $e + 1$ points of the line are $e$-close to $C$ or all of them are. Because $2e < d$, the codewords realizing the agreement, and the nearby interleaved codeword of the matrix with rows $u_0, u_1$, are unique. The argument uses no finiteness of the field beyond counting good parameters, so the same holds over any field for a set of more than $e + 1$ good parameters. Diamond and Posen remark that the same statement with identical parameters holds for affine subspaces of any dimension, by the reduction of Ben-Sasson et al. (Section 6.3); Diamond and Gruen record that Angeris, Evans and Roh extended it to the interleaved codes $C^m$ in the same range of $e$.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)

## Sources

- B. E. Diamond, J. Posen, "Proximity Testing with Logarithmic Randomness", IACR Communications in Cryptology 1(1), 2024, Section 2.1, Theorem 1 (attributed there to Roth and Zémor), with Remark 1 and Remark 2.
- B. E. Diamond, A. Gruen, "Proximity Gaps in Interleaved Codes", IACR Communications in Cryptology 1(4), 2024, Section 1.2 and Definition 1.
- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
