# Finish Merge At Preparation Traced policy Events eq nil

The finishing stage never creates logical policy events.  Directional
merge traces are event-free on this channel, while the surrounding
`merge_at` preparation already owns the single pre-trim event.
