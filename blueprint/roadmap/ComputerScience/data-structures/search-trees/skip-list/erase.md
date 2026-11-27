# Skip-list erasure

Given a key $k$ from a linearly ordered type and a skip list $S$, the
erasure of $k$ from $S$ is the skip list obtained by scanning the entries of $S$ in order: an
entry whose key is less than $k$ is kept and the scan continues; at the first entry whose key is
greater than $k$ the scan stops, and that entry and all later ones are kept; at the first entry
whose key equals $k$ that entry is removed, the scan stops, and all later entries are kept. Every
kept entry keeps its key, value and tower height.
