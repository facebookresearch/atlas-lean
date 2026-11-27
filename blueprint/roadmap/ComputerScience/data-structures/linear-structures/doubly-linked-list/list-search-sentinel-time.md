# Cost of sentinel search

If a store circularly represents the list $L$ of $n$ data nodes
with sentinel $s$, then sentinel search for a key $k$ costs exactly $2i + 4$, where $i$ is the
position, counting from $0$, of the first node of $L$ whose key is $k$, and $i = n$ if no node of
$L$ has key $k$.

That is, two units for each mismatching data node before the match plus four fixed units; an
unsuccessful search scans all $n$ data nodes.
