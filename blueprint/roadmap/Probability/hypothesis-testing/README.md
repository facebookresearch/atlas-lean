# Hypothesis testing

Tests and their validity and power: Neyman–Pearson, likelihood-ratio, score and Wald tests, monotone likelihood ratio, exact conditional tests (Fisher, Hardy–Weinberg), rank tests and ROC area (Mann–Whitney), permutation p-values, sequential tests (Wald's sequential probability ratio test) and quickest change detection (Shiryaev's rule and CUSUM), multiple testing (familywise error control by Bonferroni, Holm and closed testing; false discovery rate control by Benjamini–Hochberg; and the two-groups model with local and tail-area false discovery rates, Storey's positive false discovery rate and q-values), and meta-analysis and heterogeneity statistics.

## Multiple testing and error-rate control

These methods keep testing valid when many hypotheses are tested at once, by controlling the familywise error rate or the false discovery rate.

- [Valid p-values and false discovery proportion](valid-p-values-and-false-discovery-proportion/README.md)
- [Bonferroni correction](bonferroni-correction/README.md)
- [Holm–Bonferroni method](holm-bonferroni-method/README.md)
- [Closed testing principle](closed-testing-principle/README.md)
- [Benjamini–Hochberg procedure](benjamini-hochberg-procedure/README.md)
- [Knockoff filter](knockoff-filter/README.md)
- [Two-groups model and local false discovery rates](two-groups-model-and-local-false-discovery-rates/README.md)

## Neyman–Pearson and likelihood-based tests

These results compare hypotheses through their likelihoods: the Neyman–Pearson lemma for two simple hypotheses, monotone likelihood ratio families, the score, Wald and likelihood-ratio tests with their local power, and universal inference, which splits the sample to make likelihood-ratio sets and tests valid in finite samples without regularity.

- [Neyman–Pearson lemma](neyman-pearson-dominated-two-simple.md)
- [Monotone likelihood ratio](monotone-likelihood-ratio/README.md)
- [Score, Wald and likelihood-ratio tests](score-wald-and-likelihood-ratio-tests/README.md)
- [Local power of the likelihood-ratio test](local-power-of-the-likelihood-ratio-test/README.md)
- [Universal inference](universal-inference/README.md)

## Sequential tests and change detection

These procedures observe data one at a time and decide when to stop: Wald's sequential probability ratio test and its optimality, and the detection of a change in distribution as quickly as possible under a false-alarm constraint.

- [Sequential tests and quickest change detection](sequential-tests-and-quickest-change-detection/README.md)

## Exact, rank and randomisation inference

These procedures base inference on counts, ranks or random reassignments of the data, from exact conditional tests and rank statistics to permutation p-values and split and full conformal prediction sets.

- [Fisher's exact test](fisher-s-exact-test/README.md)
- [Exact test for Hardy–Weinberg equilibrium](exact-test-for-hardy-weinberg-equilibrium/README.md)
- [Mann–Whitney statistic and ROC area](mann-whitney-statistic-and-roc-area/README.md)
- [Permutation tests](permutation-tests/README.md)
- [Split conformal prediction](split-conformal-prediction/README.md)
- [Full conformal prediction](full-conformal-prediction/README.md)
- [Conformalized quantile regression](conformalized-quantile-regression/README.md)
- [Conformal prediction under covariate shift](conformal-prediction-under-covariate-shift/README.md)

## Other topics in hypothesis testing

Meta-analysis combines evidence from several studies and measures how much their results differ. The kernel two-sample test compares two samples through the maximum mean discrepancy between their kernel mean embeddings.

- [Meta-analysis](meta-analysis/README.md)
- [Large-deviation bound for the biased empirical MMD](measure-real-abs-mmd-biased-sub-mmd-gt-l.md)
