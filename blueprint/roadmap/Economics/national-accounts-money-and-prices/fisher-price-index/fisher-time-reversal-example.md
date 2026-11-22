# Fisher time reversal example

Concrete two-good basket: base prices `(1, 2)`, current prices `(2, 3)`, basket
`(1, 1)` in both periods. Then Laspeyres = Paasche = `5 / 3`, so the forward Fisher index
is `5 / 3` and the reversed index is `3 / 5`. Prove by applying `fisher_time_reversal`,
discharging the four positivity hypotheses with `simp [Fin.sum_univ_two]` and `norm_num`.
