# Zero Extend

Zero extension of a finite signal to a cyclic index type: the cyclic
index `i` reads source entry `i.val` when it lies below `M` and zero
otherwise. When `M ≤ N` this is a faithful extension
(`zeroExtend_natCast`, `zeroExtend_injective`). For nonzero `N` the
converse holds (`zeroExtend_injective_iff`): when `0 < N < M` it keeps
only the first `N` source entries. At `N = 0`, where `ZMod 0` is `ℤ`,
every source entry is read back at its natural index and the map is
injective for every `M`.
