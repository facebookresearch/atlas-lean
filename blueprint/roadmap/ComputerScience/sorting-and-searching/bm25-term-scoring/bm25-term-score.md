# BM25 term score

For an inverse-document-frequency weight $\mathrm{idf}$, a term frequency $\mathrm{tf}$, a saturation parameter $k_1$, a length-normalization parameter $b$, a document length $\mathrm{docLen}$ and an average document length $\mathrm{avgLen}$, the BM25 term score is

$$\mathrm{idf} \cdot \frac{\mathrm{tf} \cdot (k_1 + 1)}{\mathrm{tf} + k_1 \cdot \bigl((1 - b) + b \cdot (\mathrm{docLen} / \mathrm{avgLen})\bigr)},$$

with the [length-normalization factor](bm25-length-norm.md) in the denominator. Here $\mathrm{idf}$ is an already chosen weight, meant to be nonnegative; the raw Robertson IDF variant, which can be negative, is not used. Division is total, with $a / 0 = 0$, so the expression is defined for all real parameters.
