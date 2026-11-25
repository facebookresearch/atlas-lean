# Cache events

A cache event over a type $\alpha$ of blocks records how one request is
served: either a hit on the requested block $r \in \alpha$, or a miss on the requested block $r$
together with an optional evicted block $v \in \alpha$, absent when nothing is evicted.
