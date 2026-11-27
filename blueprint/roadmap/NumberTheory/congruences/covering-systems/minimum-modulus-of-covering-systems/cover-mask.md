# Cover Mask

The bitmask of a list of classes modulo `L`: the bitwise or, over the pairs `(r, m)` of `cs`
(standing for the class `r mod m`), of `periodicMask m (L / m) <<< r`. A set bit `n` of this mask
lies in one of the classes (`exists_mem_of_testBit_coverMask`).
