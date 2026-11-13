# Adv Of Messages

The relays of the traitors in `om` that match the messages `adv` of the traitors in
`toProtocol`: a traitor `q` relaying along the path `path ++ [q]` sends to `p` the entry at
`path.reverse` of the table it sends to `p` in round `path.length`. The empty path, which `om`
never uses, gets `default`.
