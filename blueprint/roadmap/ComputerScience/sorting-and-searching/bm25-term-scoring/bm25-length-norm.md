# BM25 length-normalization factor

With length-normalization parameter $b$, document length $\mathrm{docLen}$ and average document length $\mathrm{avgLen}$, the factor is $(1 - b) + b \cdot (\mathrm{docLen} / \mathrm{avgLen})$. On the standard BM25 domain ($\mathrm{avgLen} > 0$, $b \in [0, 1]$) this is the usual length normalization; elsewhere it is the same real expression, with division by zero giving zero, not a BM25 quantity.
