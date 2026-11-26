# Marking step

Serve a request $p$. A hit marks $p$. A miss with room loads and marks $p$. A miss with capacity
zero caches nothing. A miss on a full cache first starts a new phase, erasing every mark, if every
cached page is marked; it then evicts the page chosen by the eviction rule among the unmarked
cached pages, and loads and marks $p$.
