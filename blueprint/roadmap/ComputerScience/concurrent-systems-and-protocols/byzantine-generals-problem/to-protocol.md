# The oral messages algorithm as an oral-message protocol

For a finite set of generals, the oral messages algorithm $\mathrm{OM}(m)$ with commander $c$, as an
oral-message protocol meant to run for $m + 1$ rounds. States and messages are tables of values indexed
by relay paths, lists of generals with the latest sender first. The commander starts with its order in
every entry, and every other general with a default value in every entry. In round $r$ every general
sends its table to every general, and a receiver sets its entry at $q\tau$ to the entry at $\tau$ of the
table it got from $q$, for every sender $q$ and every path $\tau$ of length $r$; its other entries stay.
A general $p$ decides the value that $\mathrm{OM}(m)$, with commander $c$, no superiors and all the other
generals as lieutenants, gives $p$ when every value $p$ receives is read from its table: the algorithm
runs with no loyal general and with the table as the relays.
