# History

Histories from empty heaps indexed by the resulting heap, operations, insertions and actual
work. In core mode there is one linear chain and only insert, extract-min and decrease-key.
Extended mode permits cached queries and destructive meld: the two disjoint input histories
are both charged and neither input remains available in the output.
