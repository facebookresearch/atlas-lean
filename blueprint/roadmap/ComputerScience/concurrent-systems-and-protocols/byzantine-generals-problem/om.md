# The oral messages algorithm

Fix which generals are loyal and a strategy for the traitors,
which assigns a value to each list of generals and each recipient. Let $c$ be a commander holding
the value $v$, let $\sigma$ be the list of the commanders above $c$, and let $S$ be a finite set
of lieutenants. For a general $q$, let $r_q$ be the value $q$ receives from $c$: $v$ if $c$ is
loyal, and otherwise the value the strategy assigns to the list $\sigma c$ ($\sigma$ followed by
$c$) and the recipient $q$. The value that a general $p$ decides under $\mathrm{OM}(m)$ is defined
by recursion on $m$. Under $\mathrm{OM}(0)$, $p$ decides $r_p$. Under $\mathrm{OM}(m + 1)$, $p$
decides the majority of the multiset of values $w_q$ for $q \in S$, where $w_p = r_p$ and, for
$q \ne p$, $w_q$ is the value $p$ decides under $\mathrm{OM}(m)$ when $q$, holding $r_q$ with the
superiors $\sigma c$, sends it to the lieutenants $S \setminus \{q\}$.
