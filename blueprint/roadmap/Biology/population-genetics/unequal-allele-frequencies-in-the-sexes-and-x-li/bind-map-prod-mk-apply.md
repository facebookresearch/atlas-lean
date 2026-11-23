# Random union of a female and a male gamete

If the female gametes have allele law `pf`
and the male gametes allele law `pm`, the offspring ordered genotype (maternal allele, paternal
allele) has law `pf.bind fun c => pm.map (Prod.mk c)`, whose mass at `(a, b)` is
`pf a * pm b`.
