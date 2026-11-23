# The expected log-odds score is the total information content

If every column $p_i$ is a distribution on $A$, then for every real $q$

$$\sum_s \Bigl(\prod_i p_i(s_i)\Bigr) \mathrm{sc}_L(s) = \log 2 \sum_{i<w} \mathrm{IC}(p_i \,\|\, q),$$

where $L$ is the [log-odds matrix](log-odds.md), $\mathrm{sc}$ the [score](score.md) and $\mathrm{IC}$ the [information content](info-content.md).
