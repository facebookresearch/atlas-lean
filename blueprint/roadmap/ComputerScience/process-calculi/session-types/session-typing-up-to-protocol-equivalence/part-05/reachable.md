# Typing and compatibility persist along finite executions

Let $n$ be a natural number, $\Delta$ a semantically compatible ownership context and $p$, $q$
processes such that $\Delta \vdash^{\simeq}_n p$ and $q$ is reachable from $p$ by finitely many
(possibly zero) reduction steps. Then there is a semantically compatible ownership context $\Xi$
with $\Xi \vdash^{\simeq}_n q$ that is reachable from $\Delta$ by finitely many (possibly zero)
semantic advances (each advancing an endpoint and its opposite past a matching send and receive).
