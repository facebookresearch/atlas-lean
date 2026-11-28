# Heapsort with bottom-up heap construction

For a list $xs$ of elements of a linearly
ordered type, this heapsort first applies bottom-up heap construction to the array of the entries
of $xs$. Then, as long as the array is nonempty, it outputs the entry at the root (index $0$),
moves the last entry of the array to the root and deletes the last position, and sifts the new
root entry down from index $0$. The output is the list of the entries output, in the order in
which they were output.
