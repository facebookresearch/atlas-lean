# Arrhenius log10

Arrhenius log identity (base 10): the same statement as `arrhenius_log` divided by
`Real.log 10`. On coordinates, `logRatio y y_ref hy hy_ref / Real.log 10` is
`Real.logb 10 (y / y_ref)`, since `Real.logb b x = Real.log x / Real.log b`.
