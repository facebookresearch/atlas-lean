# Hypothesis-testing characterization of differential privacy

## The KOV pair condition and event bounds

- [Type-I error of a rejection set](type-i.md)
- [Type-II error of a rejection set](type-ii.md)
- [Kairouz–Oh–Viswanath tradeoff condition](kovpair.md)
- [Approximate differential privacy with finite outputs](is-approx-dpfin.md)
- [Tradeoff condition as two-sided event bounds](kovpair-iff-event-bounds.md)
- [Privacy in both orders gives the tradeoff condition](kovpair-of-is-approx-dpfin-of-swap.md)
- [The tradeoff condition at adjacent pairs gives privacy](is-approx-dpfin-of-forall-kovpair.md)
- [Approximate differential privacy is a hypothesis-testing tradeoff](is-approx-dpfin-iff-forall-kovpair.md)

## Event-form approximate differential privacy

- [Finite-sum and event forms of approximate differential privacy agree](is-approx-dpfin-iff-is-approx-dp.md)
- [Event-form approximate differential privacy as a tradeoff condition](is-approx-dp-iff-forall-kovpair.md)
- [The tradeoff condition is symmetric](kovpair-symm.md)

## Randomized tests and the tradeoff function

- [Randomized test](is-test.md)
- [Type-I error of a randomized test](alpha-of.md)
- [Type-II error of a randomized test](beta-of.md)
- [Tradeoff function](tradeoff.md)
- [Lower bounds on the tradeoff function](le-tradeoff.md)
- [A feasible test bounds the tradeoff function](tradeoff-le-beta-of.md)
- [The tradeoff function vanishes at one](tradeoff-at-one.md)
- [The tradeoff function vanishes at negative levels](tradeoff-eq-zero-of-neg.md)
- [The tradeoff function vanishes at levels at least one](tradeoff-eq-zero-of-one-le.md)

## The f-DP lower bound

- [Tradeoff lower bound of approximate differential privacy](f-eps-delta.md)
- [A test-weighted signed sum is bounded by its positive part](test-superlevel-le.md)
- [The tradeoff condition bounds the tradeoff function from below](kovpair-forward-tradeoff-ge.md)

## Converse through indicator tests

- [A rejection set bounds the tradeoff at its own level](tradeoff-indicator-upper.md)
- [A tradeoff lower bound gives the tradeoff condition](kovpair-of-tradeoff-ge.md)

## Post-processing increases the tradeoff

- [Pulling a test back through a channel](pullback-test.md)
- [Real form of composing a distribution with a channel](pmf-bind-to-real.md)
- [Pulling a test back preserves type-I error](pullback-test-alpha.md)
- [Pulling a test back preserves type-II error](pullback-test-beta.md)
- [Post-processing can only increase the tradeoff function](tradeoff-postprocess.md)

## The 3/4 versus 1/4 boundary pair on Booleans

- [Mass function three quarters on true](f-ph5.md)
- [Mass function one quarter on true](f-qh5.md)
- [Biased-bit distribution towards true](ph5.md)
- [Biased-bit distribution towards false](qh5.md)
- [The biased-bit distribution has full support](ph5-pos.md)
- [Type-I error of rejecting on false](type-i-ph5-singleton-false.md)
- [Type-II error of rejecting on false](type-ii-ph5-singleton-false.md)
- [The biased-bit pair satisfies the tradeoff condition at log 3](kovpair-ph5-qh5.md)
- [Tradeoff of the biased-bit pair at one quarter](tradeoff-ph5-qh5-quarter.md)

## Randomized-response dominance under adaptive composition

- [Rr exists channel of kovpair](rr-exists-channel-of-kovpair.md)
- [Rr Stage](rr-stage.md)
- [Is Approx DP rr Stage](is-approx-dp-rr-stage.md)
- [Rr Kfold](rr-kfold.md)
- [Rr Kfold exists channel](rr-kfold-exists-channel.md)
- [Rr Kfold tradeoff le](rr-kfold-tradeoff-le.md)
- [Kovpair kfold of rr Kfold](kovpair-kfold-of-rr-kfold.md)
- [Is Approx DP kfold of rr Kfold](is-approx-dp-kfold-of-rr-kfold.md)
