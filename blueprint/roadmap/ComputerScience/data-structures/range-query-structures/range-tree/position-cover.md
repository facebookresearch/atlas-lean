# Position Cover

Emit the wholly contained canonical nodes in left-to-right order. A difference list avoids
copying an already-built prefix at each split. Use fuel `h` such that `i.len ≤ 2 ^ h`.
