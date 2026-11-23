# Case Control

The law of a **case-control sample** with case fraction `P`: the population law `μ`
reweighted so that cases `{t ≤ L}` have total mass `P` and controls `1 - P`, keeping the
conditional laws within cases and within controls. This holds when `0 < μ{t ≤ L} < 1` and
`0 ≤ P ≤ 1` (`isProbabilityMeasure_caseControl`, `measureReal_case_caseControl`); outside that
range Lean's division by zero and `toNNReal` change the weights.
