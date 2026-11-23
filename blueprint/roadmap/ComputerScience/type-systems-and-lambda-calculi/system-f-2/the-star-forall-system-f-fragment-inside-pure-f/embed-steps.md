# Embedding preserves multistep evaluation

For System F terms $t, t' \in \mathrm{Tm}_{n,m}$ with $t \to^* t'$ ([multi-step
evaluation](../../system-f/call-by-value-safety-for-pure-system-f/steps.md)), $\mathcal{E}(t')$ is
reachable from $\mathcal{E}(t)$ by finitely many (possibly zero) [Fω weak call-by-value
steps](../conversion-aware-weak-call-by-value-safety-for-p/step.md) ([embedding](embed-2.md)).
