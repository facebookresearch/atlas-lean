# Bar Face App

Component formula for faces: extracted to avoid self-reference while defining `barFace`.
The right endpoint `d₀` is the recursive iterated right action
`rightActionPow T R n (L a)`, avoiding `eqToHom` transports while keeping
left-associated `monadPow`. The left endpoint `d_{n+1}` is the left action.
Interior faces use the public reversed-position wrapper `barMuAtPos`, i.e.
`muAtPos` with `Fin.rev`.
