# Relation denoted by a PDL program

In a model $M$, each program $\alpha$ denotes a binary
relation $R_\alpha$ on worlds: an atomic action $a$ denotes its accessibility relation $R_a$;
$(w, v) \in R_{\alpha;\beta}$ iff $(w, u) \in R_\alpha$ and $(u, v) \in R_\beta$ for some world
$u$; $R_{\alpha \cup \beta} = R_\alpha \cup R_\beta$; $R_{\alpha^*}$ is the reflexive-transitive
closure of $R_\alpha$; and $(w, v) \in R_{\varphi?}$ iff $w = v$ and $\varphi$ holds at $w$ in
$M$.
