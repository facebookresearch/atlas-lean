# LRU cache lookup

Looking up a key $k$ in an LRU cache returns an optional value
together with a cache. If the cache stores a binding $(k, v)$, the result is $v$ together
with the cache in which that binding is moved to the front and the other entries keep their
order; otherwise the result is no value together with the unchanged cache.
