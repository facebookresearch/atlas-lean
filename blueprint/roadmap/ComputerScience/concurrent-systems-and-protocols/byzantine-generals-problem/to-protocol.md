# To Protocol

The oral messages algorithm `OM(m)` with commander `c`, as an `OralProtocol` meant to run for
`m + 1` rounds. States and messages are tables of values indexed by relay paths, latest sender
first. The commander starts with its order in every entry, and every other general with
`default` in every entry. In round `r` every general sends its table to every general, and a
receiver sets its entry at `q :: τ` to the entry at `τ` of the table it got from `q`, for every
sender `q` and every path `τ` of length `r`; its other entries stay. A general `p` decides the
value `om` gives for commander `c` and lieutenants `Finset.univ.erase c` when every value `p`
receives is read from its table: `om` runs with no loyal general and with the table as the
relays.
