# Sex-differential viability selection makes the sexes' allele frequencies differ

At an autosomal biallelic locus, let newborns of both sexes have the same genotype distribution $G$ on $AA, Aa, aa$, with
allele frequency $p_0$, and let viabilities be $1 + s a_g$ in males and $1 + s b_g$ in females, with $|a_g|, |b_g| \le B$ and
$0 \le sB \le \frac12$. Let $p_m$ and $p_f$ be the frequencies of $A$ among surviving males and females, where $A$ counts $1$, $\tfrac12$, $0$
in $AA$, $Aa$, $aa$. Then

$$|p_m - p_0| \le 2Bs, \qquad |p_f - p_0| \le 2Bs, \qquad |p_m - p_f| \le 4Bs,$$

because $p_m - p_0 = s\,\mathbb E_G[(q - p_0) a] / \mathbb E_G[1 + s a]$ with $|q - p_0| \le 1$ and $\mathbb E_G[1 + sa] \ge \frac12$. The gap is created by
unequal selection, and equal viability vectors give $p_m = p_f$. Random union of the surviving gametes gives genotype
frequencies that deviate from Hardy–Weinberg proportions at $\bar p = (p_m + p_f)/2$ by
$\bigl(-\tfrac{d^2}{4}, +\tfrac{d^2}{2}, -\tfrac{d^2}{4}\bigr)$ with $d = p_m - p_f$, the [heterozygote excess](offspring-heterozygote-excess.md) of unequal frequencies in the
sexes, so the total-variation distance from Hardy–Weinberg proportions is $d^2/2 \le 8B^2 s^2$. For example $p_m = 1$, $p_f = 0$
gives deviations $\bigl(-\tfrac14, +\tfrac12, -\tfrac14\bigr)$ and distance $\tfrac12$. This $O(d^2)$ bound applies to
unordered genotypes only; genotypes ordered by parental origin can deviate by $O(d)$.

## Depends on

- [One generation of haploid selection](../natural-selection-fisher-s-theorem-and-the-price/select.md)

## Proof depends on

- [First-generation heterozygote excess from the parental genotype laws](offspring-heterozygote-excess.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section I.8 (different gene frequencies in the two sexes: random union gives an excess of heterozygotes). The selection bound is derived above.
