# Winning strategies stay winning along consistent moves

Let $M$ be a Kripke model,
$\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the model-checking game on
$M$. If $\sigma$ wins from a position $p$ in $\mathit{env}$, and $q$ is a position reachable from
$p$ by one move that is the position chosen by $\sigma$ at $p$ whenever Verifier owns $p$, then
$\sigma$ also wins from $q$ in $\mathit{env}$.
