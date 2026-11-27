# Logging an embedded computation

Fix types $X$ of queries and $Y$ of answers, a sampling family and a randomized oracle $O$ from $X$ to distributions on $Y$. For every single-oracle computation $c$ without sampling, the [logged run](m-eval-log.md) of its [embedding](embed.md) and the logged run of $c$ against $O$ have the same distribution on pairs (result, ordered list of query and answer pairs). The equality is of the joint law, so the correlation between the result and the log is preserved.
