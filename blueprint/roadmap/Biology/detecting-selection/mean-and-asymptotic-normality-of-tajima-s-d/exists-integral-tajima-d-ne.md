# Tajima's D can have positive mean while its numerator has mean zero

There is a probability law on two outcomes, with `S = 1` or `S = 2` on each, under which, for
`n = 4` genes, Tajima's numerator `N = π - S / a₁` has mean `0` while
[Tajima's D](../tajima-s-d/tajima-d.md) `D = N / √V`, with `V = e₁ S + e₂ S (S - 1)`, has
positive mean; in particular `E[D] ≠ E[N] / E[√V] = 0`. One such law: one doubleton site
(`S = 1`, `π = 2 · 2 / 6 = 2/3`) with probability `3/7`, and two singleton sites (`S = 2`,
`π = 2 · 3 / 6 = 1`) with probability `4/7`. Here `N = 4/33` and `N = -1/11` respectively, so
`E[N] = 0`, but the negative value of `N` is divided by the larger denominator. The law is not
that of the neutral coalescent: the point is that `E[N] = 0`, which holds under the neutral model
([Tajima's numerator has mean zero](../../coalescent-theory/segregating-sites-and-pairwise-differences/integral-tajima-numerator.md)),
does not by itself force `E[D] = 0`.
