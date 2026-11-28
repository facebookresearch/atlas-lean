# Cache coherence at epoch boundaries

A valid token budget rules out concurrent access
by any other core when a core can write. Separately, if the initial or last-written value is
carried forward and every readable copy matches the start value, then every reader sees that
carried value. The token permissions alone impose no equality on the copies.
