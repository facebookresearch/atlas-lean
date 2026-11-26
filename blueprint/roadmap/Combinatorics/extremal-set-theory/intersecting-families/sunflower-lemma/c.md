# Sunflower constant

One choice of the absolute constant in the [Alweiss–Lovett–Wu–Zhang bound](theorem-1-4.md)
is $C=2^{14}=16384$. It is independent of the petal count $r$, the width $w$, and the finite
ground set. Theorem 1.4 does not specify a numerical value.

For a family of distinct sets of size exactly $w$, Kupavskii and Zakharov give the strict
threshold $(2^{10}r\log_2(wr))^w$. For every $r\ge3$ and $w\ge2$, write $L=\log_{1.9}w$.
Then $L\ge1$, and $\log_2(wr)\le L+r\le r^2 L$. Also $1.9^{17}<2^{16}$ and
$1.9<(17/16)^{16}$, so $L\ge\log_{1.9}2>17/16$ and $16\log_{1.9} L>1$. Thus

$$
(2^{10} r\log_2(wr))^w < (2^{14} r^3 L\log_{1.9}L)^w.
$$

In particular, *at least* the latter number is *more than* the former, even at $w=2$.
For sets of size at most $w$, pad each member $A$ with $w-|A|$ new points belonging only to
that member. The padded ground set is still finite. Restriction to the original ground set
recovers the distinct members and preserves pairwise and total intersections of two or more
members, so an $r$-sunflower in the padded family gives one in the original family.

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, and Jiapeng Zhang, [*Improved bounds for the sunflower lemma*](https://arxiv.org/abs/1908.08483v3), Annals of Mathematics 194 (3), 2021, Theorem 1.4 and the following logarithm convention; §1.1 for private padding. The statement is also used in the [AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge) and the lean-eval problem `annals_improved_bounds_sunflower_lemma`.
- Andrey Kupavskii and Dmitrii Zakharov, [*Spread approximations for forbidden intersections problems*](https://arxiv.org/abs/2203.13379v3), §2, equation (1) and the sentence following it.
