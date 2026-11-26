# Mk Heap

The counted bottom-up heap construction of a vector of size $n$: it applies the counted sift-down to every index $i < \lfloor n/2 \rfloor$ in descending order, passing the returned vector from one call to the next and adding up the costs (comparisons, swaps). For $n \le 1$ there is no visit.
