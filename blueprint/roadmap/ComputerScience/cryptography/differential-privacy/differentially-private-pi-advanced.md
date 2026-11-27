# Advanced composition

Let the neighbouring relation be symmetric, and let $\varepsilon, \delta \ge 0$ and $0 < \delta' < 1$. If
each of $k$ mechanisms with values in probability measures is $(\varepsilon, \delta)$-differentially
private, then running them independently is $(\varepsilon', k\delta + \delta')$-differentially private
with

$$
\varepsilon' = \sqrt{2k \ln(1/\delta')}\,\varepsilon + k\varepsilon(e^{\varepsilon} - 1).
$$

The statement also holds for $\delta' \ge 1$, trivially: then $k\delta + \delta' \ge 1$ bounds every
probability, and the square root, of the nonpositive number $2k \ln(1/\delta')$, is read as $0$.

For $k \ge 1$, $\delta' \le 1/e$ and $\varepsilon \le 1/\sqrt{k}$, the second term
$k\varepsilon(e^\varepsilon - 1) \le (e - 1)\, k \varepsilon^2 \le (e - 1) \sqrt{k}\,\varepsilon$ is at most a
constant multiple of the first, so the privacy loss is of order $\sqrt{k \ln(1/\delta')}\,\varepsilon$
instead of the $k\varepsilon$ of basic composition. The
symmetry of the relation is needed: the proof uses the privacy bound in both directions between
neighbours (Lemma 3.18 of the source), and for a one-way relation the conclusion can fail. The
source, whose neighbouring histograms form a symmetric relation, proves the theorem for $k$-fold *adaptive* composition, where an adversary
chooses each mechanism after seeing the previous outputs; the statement above is the special case
of independent mechanisms. The proof bounds the expected privacy loss of each step by
$\varepsilon(e^{\varepsilon} - 1)$ and concentrates the sum of the losses with Azuma's inequality.

## Background

- [Basic composition](differentially-private-pi.md): the linear bound that advanced composition improves.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.20 (advanced composition) with Section 3.5.1 (max divergence, Lemma 3.17), Lemma 3.18 and Lemma 3.19 (Azuma's inequality).
