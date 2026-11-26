# Graphical Granger models of gene regulation

A graphical Granger model represents a $p$-gene expression time course as a vector autoregression in which gene $j$ at lag $t$ is a Granger cause of gene $i$ when the corresponding coefficient is nonzero. Penalized regression estimates the sparse lagged network; the truncating lasso adds a penalty that grows when an estimated lag carries few edges, so that it also estimates the autoregressive order.

- [Truncating lasso estimator of a graphical Granger model](truncating-lasso-estimator-of-a-graphical-granger-model.md)
- [Consistency of the truncating adaptive lasso](consistency-of-the-truncating-adaptive-lasso.md)
