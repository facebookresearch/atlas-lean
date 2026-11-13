# The Weibull law

**The Weibull law** with shape `k` and scale `l`: the measure with Lebesgue density
`weibullPDFReal k l`. It is a probability measure for `k, l > 0`
(`isProbabilityMeasure_weibullMeasure`). Outside that range the definition is totalized to the
zero measure, as `snedecorFMeasure` is with zero degrees of freedom.
