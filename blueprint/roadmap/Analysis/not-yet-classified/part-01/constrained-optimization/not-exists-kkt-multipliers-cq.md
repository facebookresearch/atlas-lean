# Not exists kkt multipliers cq

The KKT conditions fail at the minimizer of the countermodel (MF11.3c): the conclusion of
`MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality` is false although `0`
is a (global, hence local) minimizer. KKT necessity needs a constraint qualification.
