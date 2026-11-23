# Patterson Dilog

Patterson's `dilog` (Equation 16), defined here by
`pattersonDilog x = Real.li2PowerSeries (1 - x)`, using the generic dilogarithm power-series API in
`MathlibExt.Analysis.SpecialFunctions.Dilog`. Patterson's own definition is the
integral `∫₁ˣ (log t) / (1 - t) dt`; `pattersonDilog_eq_integral` proves that the
two agree on `(0, 1)`. This is his sign and normalization convention:
`dilog 1 = 0`, derivative `log x / (1 - x)` on `(0, 1)`. In classical notation
`pattersonDilog x = Li₂(1 - x)` (Maple's `dilog`).
