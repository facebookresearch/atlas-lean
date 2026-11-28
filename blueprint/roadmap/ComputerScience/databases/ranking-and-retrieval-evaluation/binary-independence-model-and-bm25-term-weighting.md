# Binary independence model and BM25 term weighting

This node collects the binary independence model (BIM) and the properties of the BM25 term weight as
separate results.

## Expansion

A sound expansion has separate pages for:

1. **BIM retrieval status value.** Under the assumptions that term occurrences are independent given
   relevance and given non-relevance, and that every term not in the query occurs with the same
   probability in relevant and non-relevant documents ($p_t = u_t$, so its likelihood ratio is $1$),
   and that the prior probability of relevance satisfies $0 < P(R = 1) < 1$ (otherwise every posterior odds
   ties while the sum still varies), ranking documents by the log-odds of relevance is rank-equivalent to ranking by
   $\sum_{t \in q \cap d} \log \frac{p_t (1 - u_t)}{u_t (1 - p_t)}$, with $p_t, u_t \in (0,1)$ the occurrence
   probabilities of $t$ in relevant and non-relevant documents. Conditional independence alone does not
   give a sum over query terms only: a term outside the query with $p_t \ne u_t$ contributes its own
   summand.
2. **BM25 weight.** For $k_1 > 0$, $0 \le b \le 1$, document length $dl \ge 0$ and average length
   $avdl > 0$, let $K = k_1\bigl((1-b) + b\, dl/avdl\bigr)$, assumed positive (this excludes only
   $b = 1$ with $dl = 0$), and $w(tf) = \mathrm{idf}(t) \cdot tf (k_1 + 1)/(tf + K)$ for $tf \ge 0$.
3. **Shape when $\mathrm{idf}(t) > 0$.** $w$ is nondecreasing and concave in $tf$, satisfies
   $w(tf) < (k_1 + 1)\,\mathrm{idf}(t)$ and tends to that value as $tf \to \infty$; for $b > 0$ and
   $tf > 0$ it is decreasing in $dl$. When $\mathrm{idf}(t) < 0$, which some IDF formulas produce for
   very common terms, every inequality reverses: with $\mathrm{idf} = -1$, $k_1 = 1$ and $b = 0$ the
   weights at $tf = 0, 1, 2$ are $0, -1, -4/3$.
4. **Binary limit.** As $k_1 \to 0$, $w(tf) \to \mathrm{idf}(t)$ for $tf > 0$ and $w(0) = 0$, so BM25
   reduces to binary term weighting.

## Sources

- S. Robertson and H. Zaragoza, *The probabilistic relevance framework: BM25 and beyond*, Foundations and
  Trends in Information Retrieval 3(4), 2009, Section 2 (equation (2.5) and the assumption on non-query terms). <https://dmice.ohsu.edu/bedricks/courses/cs635/pdf/robertson_zaragoza_2009.pdf>
- CS 276 Information Retrieval and Web Search, course schedule, Stanford University.
  <https://web.stanford.edu/class/cs276/course_schedule.html> Background reference.
