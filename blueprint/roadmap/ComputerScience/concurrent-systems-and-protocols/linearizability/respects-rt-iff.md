# Respecting real-time order, stated with positions

Let $L$ be a list of operation records, each with an invocation time strictly less than its response time. The list respects real-time order, meaning that no operation appears after an operation that was invoked after it responded, exactly when the following holds: for all positions $i, j$ of $L$, if the operation at position $i$ responds strictly before the operation at position $j$ is invoked, then $i < j$.
