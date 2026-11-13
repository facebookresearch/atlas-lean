# Length separation

Messages of different lengths below `2 ^ L` have different length
fields, hence different padded strings. This is the bit-level counterpart of the hypothesis
`lenBlock M.length = lenBlock M'.length → M.length = M'.length` of
`Cslib.Crypto.MerkleDamgard.findCollision_spec`.
