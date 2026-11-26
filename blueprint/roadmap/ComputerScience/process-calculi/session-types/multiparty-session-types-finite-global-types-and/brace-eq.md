# Brace equality of local types

Let participants, payload sorts and labels have decidable equality. Brace equality of local types is the Boolean test that two local types have the same constructors, peers and payloads, with the branches of each choice compared up to order. It reads the source's side condition of identical end-point types for plain merging over brace families. On branch lists with distinct labels it is equality up to reordering of branches; on lists with repeated labels it is a greedy first-match comparison with no meaning in the source.
