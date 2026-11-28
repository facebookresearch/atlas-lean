# Enumeration with linear preprocessing and constant delay

Model of computation: a random access machine with words of $O(\log n)$ bits and uniform cost, as in the
[word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md). An
enumeration problem asks, given an input $x$, to output all $y$ with $(x, y) \in R$, without repetition. It belongs to the class
$\mathrm{DelayC}_{\mathrm{lin}}$ if some algorithm outputs the first answer, or the end-of-output signal when there is no answer, within time
$O(|x|)$ (linear preprocessing), and each further answer and the final end-of-output signal within time $O(1)$ of the
previous output (constant delay). For a dynamic algorithm, an enumeration call is timed from its invocation after
preprocessing and the latest update: the first answer, or the end signal if the result is empty, comes within the
delay bound of that invocation. For conjunctive
queries the measure is data complexity: the query and the schema are fixed, so the constants may depend on the query. For a
conjunctive query $Q$, $\mathrm{Enum}\langle Q\rangle$ is the problem of listing $Q(I)$ for an input database $I$.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Sources

- N. Carmeli and M. Kröll, "Enumeration complexity of conjunctive queries with functional dependencies", *Proceedings of ICDT 2018*; arXiv:1712.07880 <https://arxiv.org/abs/1712.07880>, Section 2 (enumeration complexity, the class $\mathrm{DelayC}_{\mathrm{lin}}$).
- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Section 2 (RAM model, preprocessing time and delay).
