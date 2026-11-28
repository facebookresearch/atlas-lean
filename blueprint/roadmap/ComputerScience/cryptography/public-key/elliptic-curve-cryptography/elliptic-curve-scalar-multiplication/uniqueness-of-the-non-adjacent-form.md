# Uniqueness of the non-adjacent form

Every positive integer has exactly one non-adjacent form with nonzero leading digit.

**Theorem.** Let $a\in\mathbb{Z}_{\ge1}$. If $\sum_{i=0}^{l}a_i2^i$ and $\sum_{i=0}^{l'}a'_i2^i$ are non-adjacent forms of $a$ with $a_l\ne0$ and $a'_{l'}\ne0$, then $l=l'$ and $a_i=a'_i$ for all $i$. Together with the existence of a NAF, every positive integer has a unique NAF.

## Depends on

- [Non-adjacent form](non-adjacent-form.md)

## Proof depends on

None.

## Expansion

Read digits beyond the length as $0$. Minimal counterexample: let $a$ be the least positive integer with two distinct NAFs. If $a$ is even then $a_0=a'_0=0$ and both expansions shifted down are distinct NAFs of $a/2<a$. If $a$ is odd then $a_0,a'_0\in\{-1,1\}$ are both congruent to $a$ modulo $4$, so $a_0=a'_0$, and non-adjacency forces $a_1=a'_1=0$; the expansions from position $2$ on are distinct NAFs of $(a-a_0)/4<a$, or, when $(a-a_0)/4=0$ (that is $a=1$), both empty. Either case contradicts minimality. The leading-digit normalization rules out padding with zeros.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Lemma 11.1.8.
