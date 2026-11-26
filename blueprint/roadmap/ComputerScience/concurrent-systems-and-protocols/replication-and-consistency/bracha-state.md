# Global states of Bracha's broadcast

For parties $P$ and values $V$, a global state
records the set of triples $(p, j, m)$ such that a non-faulty party $p$ has sent the message $m$
to $j$; for each party $i$, the finite set of pairs $(q, m)$ such that $i$ has received $m$ from
$q$; and the value, if any, that $i$ has echoed, voted for and delivered.
