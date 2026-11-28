# Natural direct and indirect effects

For a treatment `X`, a mediator `Z` and an outcome `Y` of a finite recursive structural causal model
with independent noise laws, the natural direct effect
`NDE(x, x*; Y) = E(Y_{x, Z_{x*}}) - E(Y_{x*})` changes the treatment from `x*` to `x` while the
mediator keeps the value it would take under `x*`, and the natural indirect effect
`NIE(x, x*; Y) = E(Y_{x*, Z_x}) - E(Y_{x*})` changes only the value of the mediator. In the
identification results the nodes take values in a finite set, so that every sum over assignments is
finite; the noise may take infinitely many values, but its laws have finite support. With covariates
`W` at their factual values, the mediation formula identifies both from the observational law under
no-confounding conditions and positivity. For the NDE they are, for `x'` in `{x, x*}` and every
mediator value `z`: (H1) `Y_{x'z} ⫫ X | W`, no treatment-outcome confounding; (H2)
`Y_{x'z} ⫫ Z | X, W`, no mediator-outcome confounding; (H3) `Z_{x*} ⫫ X | W`, no treatment-mediator
confounding; and (H4) `Y_{x'z} ⫫ Z_{x*} | W`, the cross-world condition, where `Y_{x'z}` is the
outcome under `do(X = x', Z = z)` and `Z_{x*}` the mediator under `do(X = x*)`. The NIE needs them
at other values, and positivity in another direction, as its pages state. Positivity is stated in
neither source, and the formula fails without it. When a mediator-outcome confounder is affected by
the treatment, the NDE is not identified even from all interventional laws, as the kite
counterexample shows.

The pages cite P01, J. Pearl, *Direct and indirect effects*, UAI 2001, 411-420 (technical report
R-273, <https://ftp.cs.ucla.edu/pub/stat_ser/R273-U.pdf>), and P14, J. Pearl, *Interpretation and
identification of causal mediation*, Psychological Methods, 2014 (technical report R-389,
<https://ftp.cs.ucla.edu/pub/stat_ser/r389.pdf>). They also cite J. Pearl, *Causality*, Cambridge
University Press, 2000 (Pearl 2000), and C. Avin, I. Shpitser and J. Pearl, *Identifiability of
path-specific effects*, IJCAI 2005 (Avin, Shpitser and Pearl 2005).

## Nested counterfactuals and natural effects

- [Two-node counterfactual](counterfactual.md)
- [Nested counterfactual](nested-counterfactual.md)
- [Nested counterfactual at a known mediator value](nested-counterfactual-of-eq.md)
- [Composition](nested-counterfactual-self.md)
- [Consistency of the two-node counterfactual](counterfactual-eq-solve.md)
- [Expectation under the noise law](noise-expect.md)
- [Probability under the noise law](noise-prob.md)
- [Conditional expectation under the noise law](noise-cond-expect.md)
- [Conditional independence of functions of the noise](noise-cond-indep.md)
- [Expectation of a constant under the noise law](noise-expect-const.md)
- [Average natural direct effect](nde.md)
- [Average natural indirect effect](nie.md)
- [Total effect](te.md)
- [Total effect as NIE minus the reverse NDE](te-eq-nie-sub-nde.md)
- [Total effect as NDE minus the reverse NIE](te-eq-nde-sub-nie.md)

## Identification

- [Weight of an event](law-prob.md)
- [Weighted mean over an event](law-mean.md)
- [The mediation formula for the NDE](mediation-formula-nde.md)
- [The mediation formula for the NIE](mediation-formula-nie.md)
- [Events of the induced law are events of the noise](law-prob-induced-law.md)
- [Adjustment formula for the nested counterfactual mean](noise-expect-nested-eq-sum.md)
- [Counterfactual adjustment formula for the NDE](nde-eq-sum-counterfactual.md)
- [Experimental identification of the NDE](nde-eq-do-formula.md)
- [Identification of the NDE by the mediation formula](nde-eq-mediation-formula-nde.md)
- [Identification of the NIE by the mediation formula](nie-eq-mediation-formula-nie.md)
- [Identification of the NDE without covariates](nde-eq-mediation-formula-unadjusted.md)
- [Identification of the NIE without covariates](nie-eq-mediation-formula-unadjusted.md)
- [Identification of the NDE with nondescendant covariates](nde-eq-mediation-formula-nde-of-not-affe.md)
- [Identification of the NIE with nondescendant covariates](nie-eq-mediation-formula-nie-of-not-affe.md)
- [Identification of the NDE under A-1](nde-eq-mediation-formula-nde-a1.md)
- [Identification of the NIE under A-1](nie-eq-mediation-formula-nie-a1.md)

## The kite counterexample (P14, Fig. 10)

- [Fair coin](fair.md)
- [Two independent fair coins](unif.md)
- [Noise laws of the kite](noise.md)
- [The kite model (P14, Fig. 10)](kite.md)
- [Monotone coupling of W](w-mono.md)
- [Anti-monotone coupling of W](w-anti.md)
- [Indicator of a Boolean](bool-val.md)
- [The two kites induce the same Bayesian network](kite-induced-bayes-net-eq.md)
- [The two kites agree under every surgery](kite-do-set-induced-law-eq.md)
- [NDE of the monotone kite](nde-kite-mono.md)
- [NDE of the anti-monotone kite](nde-kite-anti.md)
- [The NDE is not identified](not-identified-on-nde-kite.md)
- [The mediation formulas in the two kites](mediation-formula-nde-kite.md)

## Related topics

- [Structural causal models and counterfactuals](../structural-causal-models-and-counterfactuals/README.md): the models, interventions and counterfactuals used here.
- [The back-door adjustment](../causal-bayesian-networks/backdoor-adjustment.md): adjustment for the effect of an intervention, which the mediation formula extends to natural effects.
- [Potential outcomes and causal identification](../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/README.md): the potential-outcome framework, which takes the counterfactual outcomes as primitive.
