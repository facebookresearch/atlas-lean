# Right Action Pow left Action

Right and left bar endpoints commute: mapping the left action through
`monadPow` at degree `n+1` and then applying `rightActionPow` at degree `n`
equals applying `rightActionPow` at degree `n+1` and then mapping the left
action through `monadPow` at degree `n`. Thin consequence of
`rightActionPow_naturality` at `L.action.app a` and the definitional
successor equation `rightActionPow_succ`.
