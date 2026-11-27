# X-linked selection and the inheritance-weighted frequency change

Use deterministic population-frequency dynamics at a biallelic X-linked
locus. Write $p_m,p_f\in[0,1]$ for allele frequencies in hemizygous males
and diploid females before selection.
Let viability selection with positive mean survival in each sex produce
frequencies $p_m^s,p_f^s$. Reproduction samples parents within each sex
without further genotype-dependent fertility, with Mendelian transmission,
no mutation and no transmission distortion. Sons receive their mother's X;
daughters receive one X from each parent. Thus

$$p'_m=p_f^s,\qquad p'_f=(p_m^s+p_f^s)/2.$$

Define the [inheritance-weighted mean](pbar.md)
$\bar p=(p_m+2p_f)/3$, and define $\bar p'$ in the same way. Exactly,

$$\bar p'-\bar p=\frac{(p_m^s-p_m)+2(p_f^s-p_f)}3.$$

No weak-selection or common-frequency approximation is needed. Without
selection it is the invariance of the weighted mean under
[X-linked transmission](step.md).

With equal positive numbers of males and females at the preselection and
next-generation census stages, these weighted means are also the allele
frequencies among all X chromosomes at those stages. With $M$ males and
$F$ females, the actual copy-weighted frequency is instead
$(Mp_m+2Fp_f)/(M+2F)$ when $M+2F>0$. Selection can change sex counts, so
the inheritance-weighted post-selection mean need not be the frequency
among all surviving X copies. The algebraic identity concerns the stated
inheritance weights, not an arbitrary census sex ratio.

## Depends on

- [X-linked transmission map](step.md)
- [Inheritance-weighted mean](pbar.md)

## Proof depends on

- [Invariance under one transmission step](pbar-step.md)

## Expansion

Apply invariance of the weighted mean to the post-selection pair, then
subtract the preselection mean and expand linearly. This is distinct from
replacing both within-sex selection changes by their values at a common
frequency $\bar p$, which requires a separately justified approximation.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, I.9, pp. 18–21, for the inheritance recursion and invariant $2p_f/3+p_m/3$. The selection identity is derived from that recursion, with its census interpretation qualified above.
