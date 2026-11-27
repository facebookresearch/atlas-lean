# Unpadding recovers the message

Let `0 < n`. If the message `M` has length less than `2 ^ L`, then joining its
padded blocks and removing the padding returns `M`: `unpad L (unblocks n
(padBlocks n L M)) = M`.
